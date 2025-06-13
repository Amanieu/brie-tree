//! Cursor types for tree traversal and manipulation.
//!
//! This module contains the implementation of the core B+ Tree algorithms.

use core::ops::Bound;
use core::ops::Deref;
use core::ptr::NonNull;
use core::{hint, mem};

use allocator_api2::alloc::Allocator;
use allocator_api2::alloc::Global;

use crate::Iter;
use crate::IterMut;
use crate::{
    BTree, BTreeInteger, BTreeKey,
    int::{int_from_key, key_from_int},
    node::{NodePool, NodePos, NodeRef},
    stack::Height,
};

/// Common base for mutable and immutable cursors.
pub(crate) struct RawCursor<K: BTreeKey, V, A: Allocator, Ref: Deref<Target = BTree<K, V, A>>> {
    /// Array of node and position pairs for each level of the tree.
    ///
    /// Invariants:
    /// - Only levels between 0 and `btree.height` are valid.
    /// - Positions in internal nodes must match the node on the next level of
    ///   the stack. This implies that positions in internal nodes must be
    ///   in-bounds.
    /// - Positions in leaf nodes must point to a valid entry *except* if the
    ///   cursor has reached the end of the tree, in which case it must point to
    ///   the first `Int::MAX` key in the node.
    ///
    /// These invariants may be temporarily violated during cursor operations.
    stack: <K::Int as BTreeInteger>::Stack,

    /// Reference to the underlying `BTree`.
    ///
    /// This is either a mutable or immutable reference depending on the type of
    /// cursor.
    btree: Ref,
}

impl<K: BTreeKey, V, A: Allocator, Ref: Deref<Target = BTree<K, V, A>>> Clone
    for RawCursor<K, V, A, Ref>
where
    Ref: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            btree: self.btree.clone(),
        }
    }
}

impl<K: BTreeKey, V, A: Allocator, Ref: Deref<Target = BTree<K, V, A>>> RawCursor<K, V, A, Ref> {
    /// Initializes a cursor to point to the given key.
    #[inline]
    fn seek(&mut self, key: <K::Int as BTreeInteger>::Raw) {
        // Go down the tree, at each internal node selecting the first sub-tree
        // with key greater than or equal to the search key. This sub-tree will
        // only contain keys less than or equal to its key.
        let mut height = self.btree.height;
        let mut node = self.btree.root;
        while let Some(down) = height.down() {
            let keys = unsafe { node.keys(&self.btree.internal) };
            let pos = unsafe { K::Int::search(keys, key) };
            self.stack[height] = (node, pos);
            node = unsafe { node.value(pos, &self.btree.internal).assume_init_read() };
            height = down;
        }

        // Select the first leaf element with key greater than or equal to the
        // search key.
        let keys = unsafe { node.keys(&self.btree.leaf) };
        let pos = unsafe { K::Int::search(keys, key) };
        self.stack[height] = (node, pos);
    }

    /// Helper function to check that cursor invariants are maintained.
    #[inline]
    fn check_invariants(&self) {
        if !cfg!(debug_assertions) {
            return;
        }

        // The element at each internal level should point to the node lower on
        // the stack.
        let mut height = Height::leaf();
        while let Some(up) = height.up(self.btree.height) {
            let (node, pos) = self.stack[up];
            let child = self.stack[height].0;
            debug_assert_eq!(
                unsafe { node.value(pos, &self.btree.internal).assume_init_read() },
                child
            );
            height = up;
        }

        // If the leaf node points to an `Int::MAX` key then so must all
        // internal nodes.
        let (node, pos) = self.stack[Height::leaf()];
        if unsafe { node.key(pos, &self.btree.leaf) } == K::Int::MAX {
            let mut height = Height::leaf();
            while let Some(up) = height.up(self.btree.height) {
                let (node, pos) = self.stack[up];
                debug_assert_eq!(unsafe { node.key(pos, &self.btree.internal) }, K::Int::MAX);
                height = up;
            }
        }

        debug_assert_eq!(self.stack[self.btree.height].0, self.btree.root);
    }

    /// Returns `true` if the cursor points to the end of the tree.
    #[inline]
    fn is_end(&self) -> bool {
        self.entry().is_none()
    }

    /// Returns the key and a reference to the key and value at the cursor
    /// position, or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    fn entry(&self) -> Option<(K, NonNull<V>)> {
        let (node, pos) = self.stack[Height::leaf()];
        let key = unsafe { node.key(pos, &self.btree.leaf) };
        let key = key_from_int(key)?;
        let value = unsafe { node.values_ptr(&self.btree.leaf).add(pos.index()) };
        Some((key, value.cast()))
    }

    /// Advances the cursor to the next element in the tree.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    fn next(&mut self) {
        assert!(!self.is_end(), "called next() on cursor already at end");

        // Increment the position in the leaf node.
        let (node, pos) = self.stack[Height::leaf()];
        debug_assert_ne!(unsafe { node.key(pos, &self.btree.leaf) }, K::Int::MAX);
        let pos = unsafe { pos.next() };
        self.stack[Height::leaf()].1 = pos;

        // If we reached the end of the leaf then we need to go up the tree to
        // find the next leaf node.
        if unsafe { node.key(pos, &self.btree.leaf) } == K::Int::MAX {
            self.next_leaf_node();
        }

        self.check_invariants();
    }

    /// Advances the cursor to the previous element in the tree.
    ///
    /// If the cursor is already at the first element of the tree then this
    /// method returns `false` and the cursor position is not moved.
    #[inline]
    fn prev(&mut self) -> bool {
        // If we are at the start of the leaf then we need to go up the tree to
        // find the previous leaf node.
        let (_node, pos) = self.stack[Height::leaf()];
        if pos.index() == 0 {
            return self.prev_leaf_node();
        }

        // Decrement the position in the leaf node.
        let pos = unsafe { pos.prev() };
        self.stack[Height::leaf()].1 = pos;

        self.check_invariants();

        true
    }

    /// Advances the cursor to the start of the next leaf node.
    ///
    /// Leaves the cursor unmodified if this is the last leaf node of the tree.
    #[inline]
    fn next_leaf_node(&mut self) {
        let mut height = Height::leaf();
        let mut node = loop {
            // If we reached the top of the tree then it means we are on the
            // last entry at all levels of the tree. We've reached the end of
            // the tree and can leave the cursor pointing on an `Int::MAX` key
            // to indicate that.
            let Some(up) = height.up(self.btree.height) else {
                return;
            };

            // The last element of an internal node has a key of `Int::MAX`. If
            // we are not at the last element then we can advance to the next
            // sub-tree and go down that one.
            let (node, pos) = &mut self.stack[up];
            if unsafe { node.key(*pos, &self.btree.internal) } != K::Int::MAX {
                *pos = unsafe { pos.next() };
                let node = unsafe { node.value(*pos, &self.btree.internal).assume_init_read() };
                break node;
            }

            // If we reached the end of an internal node, go up to the next
            // level to find a sub-tree to go down.
            height = up;
        };

        // We found a sub-tree, now go down all the way to a leaf node. Since
        // these nodes are guaranteeed to be at least half full we can safely
        // read the first element.
        while let Some(down) = height.down() {
            self.stack[height] = (node, pos!(0));
            node = unsafe { node.value(pos!(0), &self.btree.internal).assume_init_read() };
            height = down;
        }
        self.stack[Height::leaf()] = (node, pos!(0));

        // The tree invariants guarantee that leaf nodes are always at least
        // half full, except if this is the root node. However this can't be the
        // root node since there is more than one node.
        unsafe {
            hint::assert_unchecked(node.key(pos!(0), &self.btree.leaf) != K::Int::MAX);
        }
    }

    /// Advances the cursor to the end of the previous leaf node.
    ///
    /// Returns `false` and leaves the cursor unmodified if this is the first
    /// leaf node of the tree.
    #[inline]
    fn prev_leaf_node(&mut self) -> bool {
        let mut height = Height::leaf();
        let mut node = loop {
            // If we reached the top of the tree then it means we are on the
            // first entry at all levels of the tree. We've reached the start of
            // the tree and can leave the cursor pointing to the start of a
            // leaf node to indicate that.
            let Some(up) = height.up(self.btree.height) else {
                return false;
            };

            // If we are not at the first element then we can advance to the
            // previous sub-tree and go down that one.
            let (node, pos) = &mut self.stack[up];
            if pos.index() != 0 {
                *pos = unsafe { pos.prev() };
                let node = unsafe { node.value(*pos, &self.btree.internal).assume_init_read() };
                break node;
            }

            // If we reached the start of an internal node, go up to the next
            // level to find a sub-tree to go down.
            height = up;
        };

        // We found a sub-tree, now go down all the way to a leaf node. Since
        // these nodes are guaranteeed to be at least half full we can safely
        // read the first element.
        // TODO: Only search high half of the node.
        while let Some(down) = height.down() {
            let pos = unsafe { K::Int::search(node.keys(&self.btree.internal), K::Int::MAX) };
            self.stack[height] = (node, pos);
            node = unsafe { node.value(pos, &self.btree.internal).assume_init_read() };
            height = down;
        }
        let pos = unsafe { K::Int::search(node.keys(&self.btree.leaf), K::Int::MAX) };
        self.stack[Height::leaf()] = (node, unsafe { pos.prev() });

        // The tree invariants guarantee that leaf nodes are always at least
        // half full, except if this is the root node. However this can't be the
        // root node since there is more than one node.
        unsafe {
            hint::assert_unchecked(pos.index() != 0);
        }

        self.check_invariants();

        true
    }
}

impl<K: BTreeKey, V, A: Allocator> RawCursor<K, V, A, &'_ mut BTree<K, V, A>> {
    /// Propagates the maximum key in a leaf node to parent nodes.
    ///
    /// # Safety
    ///
    /// `key` must be the largest non-`MAX` key in the current leaf node.
    #[inline]
    unsafe fn update_leaf_max_key(&mut self, key: <K::Int as BTreeInteger>::Raw) {
        let mut height = Height::leaf();
        // This continues recursively as long as the parent sub-tree is the last
        // one in its node, or the root of the tree is reached.
        while let Some(up) = height.up(self.btree.height) {
            let (node, pos) = self.stack[up];
            if unsafe { node.key(pos, &self.btree.internal) } != K::Int::MAX {
                unsafe {
                    node.set_key(key, pos, &mut self.btree.internal);
                }
                break;
            }
            height = up;
        }
    }

    /// Common code for `insert_before` and `insert_after`.
    ///
    /// After insertion the leaf position will be unchanged.
    #[inline]
    fn insert<const AFTER: bool>(&mut self, key: K, value: V) {
        let key = int_from_key(key);
        let (node, pos) = self.stack[Height::leaf()];

        let insert_pos = if AFTER {
            assert!(
                !self.is_end(),
                "called insert_after() on cursor already at end"
            );
            unsafe { pos.next() }
        } else {
            pos
        };
        let prev_key = unsafe { node.key(insert_pos, &self.btree.leaf) };

        // If we are inserting the last key in a node then we need to update
        // the sub-tree max key in the parent.
        if prev_key == K::Int::MAX {
            if AFTER {
                unsafe {
                    self.update_leaf_max_key(key);
                }
            } else {
                // Note that because of the cursor invariants we don't need to
                // update the sub-tree keys in any parent nodes:
                // - If the cursor is at the end of the tree then all keys on
                //   the stack have value `Int::MAX` already.
                // - Otherwise the insertion doesn't happen at the end of the
                //   node, so the maximum key doesn't change.
                debug_assert!(self.is_end());
            }
        }

        // Check if this insertion will cause the leaf node to become completely
        // full. Specifically that after insertion the last key will *not* be
        // `Int::MAX`, which violates the node invariant.
        let overflow = unsafe { node.key(pos!(K::Int::B - 2), &self.btree.leaf) } != K::Int::MAX;

        // Save the next leaf pointer since it is overwritten by insertion.
        let next_leaf = unsafe { node.next_leaf(&self.btree.leaf) };

        // Insert the new key and value in the leaf. Use a fast path for
        // inserting at the end of a node. This helps with common cases when
        // appending to the end of a tree.
        if prev_key == K::Int::MAX {
            unsafe {
                node.set_key(key, insert_pos, &mut self.btree.leaf);
                node.value_mut(insert_pos, &mut self.btree.leaf)
                    .write(value);
            }
        } else {
            unsafe {
                node.insert_key(key, insert_pos, K::Int::B, &mut self.btree.leaf);
                node.insert_value(value, insert_pos, K::Int::B, &mut self.btree.leaf);
            }
        }

        // If insertion didn't overflow then we are done.
        if !overflow {
            // Restore next_leaf which will have been overwritten by the insert.
            unsafe {
                node.set_next_leaf(next_leaf, &mut self.btree.leaf);
            }
            return;
        }

        // At this point the leaf node is completely full and needs to be split
        // to maintain the node invariant.

        // Record the last key of the first half of the node. This will become
        // the key for the left sub-tree in the parent node.
        let mut mid_key = unsafe { node.key(pos!(K::Int::B / 2 - 1), &self.btree.leaf) };

        // Allocate a new node and move the second half of the current node to
        // it.
        let new_uninit_node = unsafe { self.btree.leaf.alloc_node(&self.btree.alloc) };
        let mut new_node = unsafe { node.split_into(new_uninit_node, &mut self.btree.leaf) };

        // Update the next-leaf pointers for both nodes.
        unsafe {
            new_node.set_next_leaf(next_leaf, &mut self.btree.leaf);
            node.set_next_leaf(Some(new_node), &mut self.btree.leaf);
        }

        // Keep track of where the cursor is in the tree by adjusting the
        // position on the stack if we were in the second half of the node that
        // got split.
        let mut in_right_split = if let Some(new_pos) = pos.split_right_half() {
            self.stack[Height::leaf()] = (new_node, new_pos);
            true
        } else {
            false
        };

        // Propagate the split by inserting the new node in the next level of
        // the tree. This may cause that node to also be split if it gets full.
        let mut height = Height::leaf();
        while let Some(up) = height.up(self.btree.height) {
            height = up;
            let (node, mut pos) = self.stack[height];

            // The last 2 keys of leaf nodes are always `Int::MAX` so we can
            // check if an insertion will cause an overflow by looking at
            // whether the key at `B - 3` is `Int::MAX`.
            let overflow =
                unsafe { node.key(pos!(K::Int::B - 3), &self.btree.internal) } != K::Int::MAX;

            // The existing key for this sub-tree (max of all keys in sub-tree)
            // is correct for the second node of the split. Similarly the
            // existing value already points to the first node of the split. So
            // insert the new key before the existing one and the new value
            // after the existing one.
            unsafe {
                node.insert_key(mid_key, pos, K::Int::B, &mut self.btree.internal);
                node.insert_value(new_node, pos.next(), K::Int::B, &mut self.btree.internal);
            }

            // If the node below us ended up on the right side of the split,
            // adjust the cursor position to point to the newly inserted node.
            if in_right_split {
                pos = unsafe { pos.next() };
            }
            self.stack[height].1 = pos;

            // If the node is not full then we're done.
            if !overflow {
                self.check_invariants();
                return;
            }

            // Record the last key of the first half of the node. This will
            // become the key for the left sub-tree in the parent node.
            mid_key = unsafe { node.key(pos!(K::Int::B / 2 - 1), &self.btree.internal) };

            // Set the last key of the first half to `Int::MAX` to indicate that
            // it is the last element in this node.
            unsafe {
                node.set_key(
                    K::Int::MAX,
                    pos!(K::Int::B / 2 - 1),
                    &mut self.btree.internal,
                );
            }

            // Allocate a new node and move the second half of the current node
            // to it.
            let new_uninit_node = unsafe { self.btree.internal.alloc_node(&self.btree.alloc) };
            new_node = unsafe { node.split_into(new_uninit_node, &mut self.btree.internal) };

            // Keep track of where the cursor is in the tree by adjusting the
            // position on the stack if we were in the second half of the node
            // that got split.
            in_right_split = if let Some(new_pos) = pos.split_right_half() {
                self.stack[height] = (new_node, new_pos);
                true
            } else {
                false
            };
        }

        // If we reached the root of the tree then we need to add a new level to
        // the tree and create a new root node.
        let new_uninit_root = unsafe { self.btree.internal.alloc_node(&self.btree.alloc) };

        // The new root only contains 2 elements: the original root node and the
        // newly created split node. The only non-MAX key is the first one which
        // holds the maximum key in the left sub-tree.
        let new_root;
        unsafe {
            new_root = new_uninit_root.init_keys(&mut self.btree.internal);
            new_root.set_key(mid_key, pos!(0), &mut self.btree.internal);
            new_root
                .value_mut(pos!(0), &mut self.btree.internal)
                .write(self.btree.root);
            new_root
                .value_mut(pos!(1), &mut self.btree.internal)
                .write(new_node);
        }
        self.btree.root = new_root;

        // Increment the height of the tree. The `expect` should never fail here
        // since we calculated the maximum possible height for the tree
        // statically as `Height::max`.
        self.btree.height = self
            .btree
            .height
            .up(Height::max())
            .expect("exceeded maximum height");

        // Set up the new level in the cursor stack.
        let pos = if in_right_split { pos!(1) } else { pos!(0) };
        self.stack[self.btree.height] = (new_root, pos);

        self.check_invariants();
    }

    /// Replaces the key and value of the element at the given position.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    fn replace(&mut self, key: K, value: V) -> (K, V) {
        let key = int_from_key(key);

        let (node, pos) = self.stack[Height::leaf()];
        let old_key = unsafe { node.key(pos, &self.btree.leaf) };
        let old_key = key_from_int(old_key).expect("called replace() on cursor already at end");

        // If we are replacing the last key in a node then we need to update the
        // sub-tree max key in the parent.
        unsafe {
            if node.key(pos.next(), &self.btree.leaf) == K::Int::MAX {
                self.update_leaf_max_key(key);
            }
        }

        // Then actually replace the key and value in the leaf node.
        unsafe {
            node.set_key(key, pos, &mut self.btree.leaf);
        }
        let old_value = unsafe {
            mem::replace(
                node.value_mut(pos, &mut self.btree.leaf).assume_init_mut(),
                value,
            )
        };

        (old_key, old_value)
    }

    /// Removes the element to the right of the cursor and returns it.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    fn remove(&mut self) -> (K, V) {
        let (node, pos) = self.stack[Height::leaf()];

        // Check if this deletion will cause the leaf node to become less than
        // half full. Specifically that after deletion last key in the first
        // half will be`Int::MAX`, which violates the node invariant.
        let underflow = unsafe { node.key(pos!(K::Int::B / 2), &self.btree.leaf) } == K::Int::MAX;

        // Extract the key and value that will be returned by this function.
        let key = unsafe {
            key_from_int(node.key(pos, &self.btree.leaf))
                .expect("called remove() on cursor already at end")
        };
        let value = unsafe { node.value(pos, &self.btree.leaf).assume_init_read() };

        // Remove the key and value from the node.
        unsafe {
            node.remove_key(pos, &mut self.btree.leaf);
            node.remove_value(pos, &mut self.btree.leaf);
        }

        // If we removed the last key in a node then we need to update the
        // sub-tree max key in the parent.
        unsafe {
            if node.key(pos, &self.btree.leaf) == K::Int::MAX && self.btree.height != Height::leaf()
            {
                // Leaf nodes must be at least half full if they are not the
                // root node.
                let new_max = node.key(pos.prev(), &self.btree.leaf);
                self.update_leaf_max_key(new_max);
            }
        }

        // If the leaf node is now less than half-full, we need to either steal
        // an element from a sibling node or merge it with a sibling to restore
        // the node invariant that it must always be at least half full..
        if underflow {
            // If there is only a single leaf node in the tree then it is
            // allowed to have as little as zero elements and cannot underflow.
            if let Some(up) = Height::leaf().up(self.btree.height) {
                // `node` is less than half-full, try to restore the invariant
                // by stealing from another node or merging it.
                let up_node = unsafe {
                    self.handle_underflow(Height::leaf(), up, node, true, |btree| &mut btree.leaf)
                };
                if let Some(mut node) = up_node {
                    let mut height = up;
                    loop {
                        if let Some(up) = height.up(self.btree.height) {
                            // Check if this node is less than half full. A
                            // half-full internal node would have the first
                            // `Int::MAX` key at `B / 2 - 1`.
                            if unsafe { node.key(pos!(K::Int::B / 2 - 2), &self.btree.internal) }
                                == K::Int::MAX
                            {
                                // `node` is less than half-full, try to restore
                                // the invariant by stealing from another node
                                // or merging it.
                                if let Some(up_node) = unsafe {
                                    self.handle_underflow(height, up, node, false, |btree| {
                                        &mut btree.internal
                                    })
                                } {
                                    // If the underflow was resolved by merging
                                    // then the parent node could have become
                                    // less than half-full itself. Loop back
                                    // and do the same with the parent.
                                    node = up_node;
                                    height = up;
                                    continue;
                                }
                            }
                        } else {
                            // We've reached the root node. If it only has a
                            // single element then we can pop a level off the
                            // tree and free the old root node.
                            debug_assert_eq!(node, self.btree.root);
                            if unsafe { node.key(pos!(0), &self.btree.internal) } == K::Int::MAX {
                                unsafe {
                                    self.btree.root = node
                                        .value(pos!(0), &self.btree.internal)
                                        .assume_init_read();
                                }
                                unsafe {
                                    self.btree.internal.free_node(node);
                                }
                                self.btree.height = height.down().unwrap();
                            }
                        }
                        break;
                    }
                }
            }
        }

        // If we ended up at the end of a leaf node due to the deletion, advance
        // the cursor to the next element.
        if self.is_end() {
            self.next_leaf_node();
        }

        self.check_invariants();

        (key, value)
    }

    /// Given `child` which is less than half full, restores the invariant that
    /// nodes must be at least half full by stealing an element from a sibling
    /// or merging `child` with a sibling node.
    ///
    /// If this is resolved through merging, this function returns a `NodeRef`
    /// to the parent of `child` which may now be under-filled.
    ///
    /// # Safety
    ///
    /// - `up` is the level above the one containing `child`.
    /// - `child` must have exact `B / 2 - 1` elements.
    /// - `child_is_leaf` indicates whether `child` is a leaf node and
    ///   `child_pool` returns a reference to the appropriate `NodePool`.
    #[inline]
    unsafe fn handle_underflow<ChildValue>(
        &mut self,
        height: Height<K::Int>,
        up: Height<K::Int>,
        child: NodeRef,
        child_is_leaf: bool,
        child_pool: impl Fn(&mut BTree<K, V, A>) -> &mut NodePool<K::Int, ChildValue>,
    ) -> Option<NodeRef> {
        // The child must have exactly `B / 2 - 1` elements.
        debug_assert_eq!(
            unsafe {
                if child_is_leaf {
                    child.leaf_end(&self.btree.leaf).index()
                } else {
                    child.internal_end(&self.btree.internal).index()
                }
            },
            K::Int::B / 2 - 1
        );

        // Check if the child is the last sub-tree in its parent. The last
        // sub-tree always has a key of `Int::MAX`.
        let (node, pos) = self.stack[up];
        debug_assert_eq!(
            unsafe { node.value(pos, &self.btree.internal).assume_init_read() },
            child
        );
        let child_subtree_max = unsafe { node.key(pos, &self.btree.internal) };

        // We now need to select a sibling node to steal from or merge with.
        // Prefer using the next sub-tree as a sibling since it has a more
        // efficient code path.
        if child_subtree_max != K::Int::MAX {
            let sibling = unsafe {
                node.value(pos.next(), &self.btree.internal)
                    .assume_init_read()
            };

            // We can steal from the sibling if it is more than half-full.
            let can_steal = unsafe {
                sibling.key(
                    if child_is_leaf {
                        pos!(K::Int::B / 2)
                    } else {
                        pos!(K::Int::B / 2 - 1)
                    },
                    child_pool(self.btree),
                )
            } != K::Int::MAX;

            if can_steal {
                unsafe {
                    // Remove the first key/value from the sibling.
                    let key = sibling.key(pos!(0), child_pool(self.btree));
                    let value = sibling
                        .value(pos!(0), child_pool(self.btree))
                        .assume_init_read();
                    sibling.remove_key(pos!(0), child_pool(self.btree));
                    sibling.remove_value(pos!(0), child_pool(self.btree));

                    if child_is_leaf {
                        // If the child is a leaf node then we can just insert
                        // the key/value at `B / 2 - 1` since we know the child
                        // currently has exactly that many elements.
                        child.set_key(key, pos!(K::Int::B / 2 - 1), child_pool(self.btree));
                        child
                            .value_mut(pos!(K::Int::B / 2 - 1), child_pool(self.btree))
                            .write(value);
                    } else {
                        // If the child is an internal node then we need to set
                        // the key for the *previous* sub-tree (which is
                        // currently `Int::MAX`) to `child_subtree_max` which is
                        // the maximum key for that sub-tree before the steal.
                        child.set_key(
                            child_subtree_max,
                            pos!(K::Int::B / 2 - 2),
                            child_pool(self.btree),
                        );
                        child
                            .value_mut(pos!(K::Int::B / 2 - 1), child_pool(self.btree))
                            .write(value);
                    }

                    // The steal has caused the largest key in `child` to
                    // increase (since we appended to its end). Update the key
                    // for this sub-tree in the parent to the key for the stolen
                    // element.
                    node.set_key(key, pos, &mut self.btree.internal);
                }

                // Stealing can't cause recursive underflows.
                None
            } else {
                unsafe {
                    // The sibling has exactly `B / 2` elements, move those to
                    // the end of the child which has exactly `B / 2 - 1`
                    // elements. This results in a full node with the maximum of
                    // `B - 1` elements.
                    child.merge_from(
                        sibling,
                        pos!(K::Int::B / 2 - 1),
                        K::Int::B / 2,
                        child_pool(self.btree),
                    );

                    // If this is an internal node then we need to copy the
                    // previous maximum key for the child's sub-tree to slot
                    // `B / 2 - 2`  which previously contained MAX.
                    if !child_is_leaf {
                        child.set_key(
                            child_subtree_max,
                            pos!(K::Int::B / 2 - 2),
                            child_pool(self.btree),
                        );
                    }

                    // Update the next leaf pointer if this is a leaf node.
                    if child_is_leaf {
                        let next_leaf = sibling.next_leaf(child_pool(self.btree));
                        child.set_next_leaf(next_leaf, child_pool(self.btree));
                    }

                    // The sibling is no longer in the tree, free its node.
                    child_pool(self.btree).free_node(sibling);

                    // Remove the sibling node from its parent. We keep the key
                    // of `sibling` and remove that of `child` because the key
                    // should hold the maximum key in the sub-tree.
                    node.remove_key(pos, &mut self.btree.internal);
                    node.remove_value(pos.next(), &mut self.btree.internal);
                }

                // Merging may cause the parent node to become under-sized.
                Some(node)
            }
        } else {
            let sibling = unsafe {
                node.value(pos.prev(), &self.btree.internal)
                    .assume_init_read()
            };

            // We can steal from the sibling if it is more than half-full.
            let can_steal = unsafe {
                sibling.key(
                    if child_is_leaf {
                        pos!(K::Int::B / 2)
                    } else {
                        pos!(K::Int::B / 2 - 1)
                    },
                    child_pool(self.btree),
                )
            } != K::Int::MAX;

            if can_steal {
                unsafe {
                    // Find the position of the last element in the sibling.
                    let sibling_end = if child_is_leaf {
                        sibling.leaf_end(child_pool(self.btree))
                    } else {
                        sibling.internal_end(child_pool(self.btree))
                    };
                    let sibling_last = sibling_end.prev();

                    if child_is_leaf {
                        // If the child is a leaf node then we can just take the
                        // last key/value of the sibling and insert it at the
                        // start of the child.
                        //
                        // We use a node size of `B / 2 + 1` so that the
                        // operation becomes a copy of exactly `B / 2` elements.
                        // All elements in the second half of the node are
                        // absent anyways. This also preserves the next leaf
                        // pointer.
                        let key = sibling.key(sibling_last, child_pool(self.btree));
                        let value = sibling
                            .value(sibling_last, child_pool(self.btree))
                            .assume_init_read();
                        child.insert_key(key, pos!(0), K::Int::B / 2 + 1, child_pool(self.btree));
                        child.insert_value(
                            value,
                            pos!(0),
                            K::Int::B / 2 + 1,
                            child_pool(self.btree),
                        );

                        // Stealing the last element of `sibling` has caused
                        // its largest key to decrease. Update the key for this
                        // sub-tree in the parent to the key for the new last
                        // element.
                        let sibling_max_key =
                            sibling.key(sibling_last.prev(), child_pool(self.btree));
                        node.set_key(sibling_max_key, pos.prev(), &mut self.btree.internal);

                        // Now actually shrink the sibling by removing its last
                        // element.
                        sibling.set_key(K::Int::MAX, sibling_last, child_pool(self.btree));
                    } else {
                        // If the child is a internal node then we need to
                        // recover the maximum key in the sibling from `node`
                        // and insert that along with the last sub-tree in the
                        // sibling into the child.
                        //
                        // We use a node size of `B / 2 + 1` so that the
                        // operation becomes a copy of exactly `B / 2` elements.
                        // All elements in the second half of the node are
                        // absent anyways. This also preserves the next leaf
                        // pointer.
                        let sibling_max_key = node.key(pos.prev(), &self.btree.internal);
                        let value = sibling
                            .value(sibling_last, child_pool(self.btree))
                            .assume_init_read();
                        child.insert_key(
                            sibling_max_key,
                            pos!(0),
                            K::Int::B / 2 + 1,
                            child_pool(self.btree),
                        );
                        child.insert_value(
                            value,
                            pos!(0),
                            K::Int::B / 2 + 1,
                            child_pool(self.btree),
                        );

                        // Stealing the last element of `sibling` has caused
                        // its largest key to decrease. Update the key for this
                        // sub-tree in the parent to the key for the new last
                        // element.
                        let sibling_max_key =
                            sibling.key(sibling_last.prev(), child_pool(self.btree));
                        node.set_key(sibling_max_key, pos.prev(), &mut self.btree.internal);

                        // Now actually shrink the sibling by removing its last
                        // element.
                        sibling.set_key(K::Int::MAX, sibling_last.prev(), child_pool(self.btree));
                    }

                    // After stealing, we need to adjust the cursor position for
                    // the child.
                    self.stack[height].1 = self.stack[height].1.next();
                }

                // Stealing can't cause recursive underflows.
                None
            } else {
                unsafe {
                    // The child has exactly `B / 2 - 1` elements, move those to
                    // the end of the sibling which has exactly `B / 2`
                    // elements. This results in a full node with the maximum of
                    // `B - 1` elements.
                    sibling.merge_from(
                        child,
                        pos!(K::Int::B / 2),
                        K::Int::B / 2 - 1,
                        child_pool(self.btree),
                    );

                    // If this is an internal node then we need to copy the
                    // previous maximum key for the sibling's sub-tree to slot
                    // `B / 2 - 1`  which previously contained MAX.
                    if !child_is_leaf {
                        let sibling_max_key = node.key(pos.prev(), &self.btree.internal);
                        sibling.set_key(
                            sibling_max_key,
                            pos!(K::Int::B / 2 - 1),
                            child_pool(self.btree),
                        );
                    }

                    // Update the next leaf pointer if this is a leaf node.
                    if child_is_leaf {
                        let next_leaf = child.next_leaf(child_pool(self.btree));
                        sibling.set_next_leaf(next_leaf, child_pool(self.btree));
                    }

                    // The child is no longer in the tree, free its node.
                    child_pool(self.btree).free_node(child);

                    // Remove the child node from its parent. We keep the key
                    // of `child` and remove that of `sibling` because the key
                    // should hold the maximum key in the sub-tree.
                    node.remove_key(pos.prev(), &mut self.btree.internal);
                    node.remove_value(pos, &mut self.btree.internal);

                    // After merging, we need to adjust the cursor position for
                    // the child and parent.
                    self.stack[up].1 = self.stack[up].1.prev();
                    self.stack[height] = (
                        sibling,
                        NodePos::new_unchecked(self.stack[height].1.index() + K::Int::B / 2),
                    );
                }

                // Merging may cause the parent node to become under-sized.
                Some(node)
            }
        }
    }
}

/// A cursor over the elements of a [`BTree`].
///
/// Cursors point either to an element in the tree or to the end of the tree.
///
/// Iterators are more efficient than cursors. Prefer using them if you don't
/// need reverse iteration or if you don't need to insert or remove elements in
/// the tree.
///
/// This type is returned by [`BTree::cursor_at`] and [`BTree::cursor`].
pub struct Cursor<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawCursor<K, V, A, &'a BTree<K, V, A>>,
}

impl<K: BTreeKey, V, A: Allocator> Clone for Cursor<'_, K, V, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> Cursor<'a, K, V, A> {
    /// Returns `true` if the cursor points to the end of the tree.
    #[inline]
    pub fn is_end(&self) -> bool {
        self.raw.is_end()
    }

    /// Returns the key of the element that the cursor is currently pointing to,
    /// or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn key(&self) -> Option<K> {
        self.entry().map(|(k, _v)| k)
    }

    /// Returns a reference to the value that the cursor is currently
    /// pointing to, or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn value(&self) -> Option<&'a V> {
        self.entry().map(|(_k, v)| v)
    }

    /// Returns the key and a reference to the value that the cursor is
    /// currently pointing to, or `None` if the cursor is pointing to the end of
    /// the tree.
    #[inline]
    pub fn entry(&self) -> Option<(K, &'a V)> {
        self.raw.entry().map(|(k, v)| (k, unsafe { v.as_ref() }))
    }

    /// Advances the cursor to the next element in the tree.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn next(&mut self) {
        self.raw.next();
    }

    /// Advances the cursor to the previous element in the tree.
    ///
    /// If the cursor is already at the first element of the tree then this
    /// method returns `false` and the cursor position is not moved.
    #[inline]
    pub fn prev(&mut self) -> bool {
        self.raw.prev()
    }

    /// Returns an iterator starting a the current element.
    ///
    /// Iterators are more efficient than cursors. Prefer using them if you don't
    /// need reverse iteration or if you don't need to insert or remove elements in
    /// the tree.
    #[inline]
    pub fn iter(&self) -> Iter<'a, K, V, A> {
        let (node, pos) = self.raw.stack[Height::leaf()];
        Iter {
            raw: crate::RawIter { node, pos },
            btree: self.raw.btree,
        }
    }
}

/// A mutable cursor over the elements of a [`BTree`] which allows editing
/// operations.
///
/// Cursors point either to an element in the tree or to the end of the tree.
///
/// Iterators are more efficient than cursors. Prefer using them if you don't
/// need reverse iteration or if you don't need to insert or remove elements in
/// the tree.
///
/// This type is returned by [`BTree::cursor_mut_at`] and [`BTree::cursor_mut`].
pub struct CursorMut<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawCursor<K, V, A, &'a mut BTree<K, V, A>>,
}

impl<'a, K: BTreeKey, V, A: Allocator> CursorMut<'a, K, V, A> {
    /// Internal constructor for an uninitialized cursor.
    ///
    /// This allows cursors to be initialized in-place, which works around
    /// rustc's poor support for move-elimination.
    ///
    /// # Safety
    ///
    /// The cursor must be initialized before use by calling `seek`.
    #[inline]
    pub(crate) unsafe fn uninit(btree: &'a mut BTree<K, V, A>) -> Self {
        Self {
            raw: RawCursor {
                stack: <K::Int as BTreeInteger>::Stack::default(),
                btree,
            },
        }
    }

    /// Initializes a cursor to point to the given key.
    #[inline]
    pub(crate) fn seek(&mut self, key: <K::Int as BTreeInteger>::Raw) {
        self.raw.seek(key);
    }

    /// Returns `true` if the cursor points to the end of the tree.
    #[inline]
    pub fn is_end(&self) -> bool {
        self.entry().is_none()
    }

    /// Returns the key of the element that the cursor is currently pointing to,
    /// or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn key(&self) -> Option<K> {
        self.entry().map(|(k, _v)| k)
    }

    /// Returns a reference to the value that the cursor is currently
    /// pointing to, or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn value(&self) -> Option<&V> {
        self.entry().map(|(_k, v)| v)
    }

    /// Returns a mutable reference to the value that the cursor is currently
    /// pointing to, or `None` if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn value_mut(&mut self) -> Option<&mut V> {
        self.entry_mut().map(|(_k, v)| v)
    }

    /// Returns the key and a reference to the value that the cursor is
    /// currently pointing to, or `None` if the cursor is pointing to the end of
    /// the tree.
    #[inline]
    pub fn entry(&self) -> Option<(K, &V)> {
        self.raw.entry().map(|(k, v)| (k, unsafe { v.as_ref() }))
    }

    /// Returns the key and a mutable reference to the value that the cursor is
    /// currently pointing to, or `None` if the cursor is pointing to the end of
    /// the tree.
    #[inline]
    pub fn entry_mut(&mut self) -> Option<(K, &mut V)> {
        self.raw
            .entry()
            .map(|(k, mut v)| (k, unsafe { v.as_mut() }))
    }

    /// Advances the cursor to the next element in the tree.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn next(&mut self) {
        self.raw.next();
    }

    /// Advances the cursor to the previous element in the tree.
    ///
    /// If the cursor is already at the first element of the tree then this
    /// method returns `false` and the cursor position is not moved.
    #[inline]
    pub fn prev(&mut self) -> bool {
        self.raw.prev()
    }

    /// Returns an iterator starting a the current element.
    ///
    /// Iterators are more efficient than cursors. Prefer using them if you don't
    /// need reverse iteration or if you don't need to insert or remove elements in
    /// the tree.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V, A> {
        let (node, pos) = self.raw.stack[Height::leaf()];
        Iter {
            raw: crate::RawIter { node, pos },
            btree: self.raw.btree,
        }
    }

    /// Returns a mutable iterator starting a the current element.
    ///
    /// Iterators are more efficient than cursors. Prefer using them if you don't
    /// need reverse iteration or if you don't need to insert or remove elements in
    /// the tree.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, A> {
        let (node, pos) = self.raw.stack[Height::leaf()];
        IterMut {
            raw: crate::RawIter { node, pos },
            btree: self.raw.btree,
        }
    }

    /// Returns an iterator starting a the current element.
    ///
    /// Unlike [`CursorMut::iter`] the returned iterator has the same lifetime
    /// as the cursor and consumes the cursor.
    ///
    /// Iterators are more efficient than cursors. Prefer using them if you don't
    /// need reverse iteration or if you don't need to insert or remove elements in
    /// the tree.
    #[inline]
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> Iter<'a, K, V, A> {
        let (node, pos) = self.raw.stack[Height::leaf()];
        Iter {
            raw: crate::RawIter { node, pos },
            btree: self.raw.btree,
        }
    }

    /// Returns a mutable iterator starting a the current element.
    ///
    /// Unlike [`CursorMut::iter_mut`] the returned iterator has the same lifetime
    /// as the cursor and consumes the cursor.
    ///
    /// Iterators are more efficient than cursors. Prefer using them if you don't
    /// need reverse iteration or if you don't need to insert or remove elements in
    /// the tree.
    #[inline]
    pub fn into_iter_mut(self) -> IterMut<'a, K, V, A> {
        let (node, pos) = self.raw.stack[Height::leaf()];
        IterMut {
            raw: crate::RawIter { node, pos },
            btree: self.raw.btree,
        }
    }

    /// Inserts `key` and `value` before the element that the cursor is
    /// currently pointing to.
    ///
    /// After insertion the cursor will be pointing to the newly inserted
    /// element.
    ///
    /// If the cursor is pointing to the end of the tree then this inserts the
    /// new element at the end of the tree after all other elements.
    ///
    /// It is the user's responsibility to ensure that inserting `key` at this
    /// position does not violate the invariant that all keys must be in sorted
    /// order in the tree. Violating this invariant is safe but may cause
    /// other operations to return incorrect results or panic.
    #[inline]
    pub fn insert_before(&mut self, key: K, value: V) {
        self.raw.insert::<false>(key, value);
    }

    /// Inserts `key` and `value` after the element that the cursor is
    /// currently pointing to.
    ///
    /// After insertion the cursor will still be pointing to the same element as
    /// before the insertion.
    ///
    /// It is the user's responsibility to ensure that inserting `key` at this
    /// position does not violate the invariant that all keys must be in sorted
    /// order in the tree. Violating this invariant is safe but may cause
    /// other operations to return incorrect results or panic.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn insert_after(&mut self, key: K, value: V) {
        self.raw.insert::<true>(key, value);
    }

    /// Replaces the key and value of the element that the cursor is currently
    /// pointing to and returns the previous key and value.
    ///
    /// It is the user's responsibility to ensure that inserting `key` at this
    /// position does not violate the invariant that all keys must be in sorted
    /// order in the tree. Violating this invariant is safe but may cause
    /// other operations to return incorrect results or panic.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn replace(&mut self, key: K, value: V) -> (K, V) {
        self.raw.replace(key, value)
    }

    /// Removes the element that the cursor is currently pointing to and returns
    /// it.
    ///
    /// After removal the cursor will point to the element after the current
    /// one.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is pointing to the end of the tree.
    #[inline]
    pub fn remove(&mut self) -> (K, V) {
        self.raw.remove()
    }
}

impl<K: BTreeKey, V, A: Allocator> BTree<K, V, A> {
    /// Returns a [`RawCursor`] pointing at the first element of the tree.
    #[inline]
    fn raw_cursor<Ref: Deref<Target = Self>>(btree: Ref) -> RawCursor<K, V, A, Ref> {
        let mut stack = <K::Int as BTreeInteger>::Stack::default();

        // Go down the tree, at each internal node selecting the first sub-tree.
        let mut height = btree.height;
        let mut node = btree.root;
        while let Some(down) = height.down() {
            stack[height] = (node, pos!(0));
            node = unsafe { node.value(pos!(0), &btree.internal).assume_init_read() };
            height = down;
        }

        // The first leaf node is always the left-most leaf on the tree and is
        // never deleted.
        debug_assert_eq!(node, NodeRef::zero());
        stack[height] = (NodeRef::zero(), pos!(0));
        RawCursor { stack, btree }
    }

    /// Returns a [`RawCursor`] pointing at the first element with key greater
    /// than `bound`.
    #[inline]
    fn raw_cursor_at<Ref: Deref<Target = Self>>(
        btree: Ref,
        key: <K::Int as BTreeInteger>::Raw,
    ) -> RawCursor<K, V, A, Ref> {
        let stack = <K::Int as BTreeInteger>::Stack::default();
        let mut cursor = RawCursor { stack, btree };
        cursor.seek(key);
        cursor
    }

    /// Returns a [`Cursor`] pointing at the first element of the tree.
    #[inline]
    pub fn cursor(&self) -> Cursor<'_, K, V, A> {
        let raw = Self::raw_cursor(self);
        Cursor { raw }
    }

    /// Returns a [`Cursor`] pointing at the first element with key greater
    /// than `bound`.
    #[inline]
    pub fn cursor_at(&self, bound: Bound<K>) -> Cursor<'_, K, V, A> {
        let key = match bound {
            Bound::Included(key) => int_from_key(key),
            Bound::Excluded(key) => K::Int::increment(int_from_key(key)),
            Bound::Unbounded => K::Int::MAX,
        };
        let raw = Self::raw_cursor_at(self, key);
        Cursor { raw }
    }

    /// Returns a [`CursorMut`] pointing at the first element of the tree.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, K, V, A> {
        let raw = Self::raw_cursor(self);
        CursorMut { raw }
    }

    /// Returns a [`CursorMut`] pointing at the first element with key greater
    /// than `bound`.
    #[inline]
    pub fn cursor_mut_at(&mut self, bound: Bound<K>) -> CursorMut<'_, K, V, A> {
        let key = match bound {
            Bound::Included(key) => int_from_key(key),
            Bound::Excluded(key) => K::Int::increment(int_from_key(key)),
            Bound::Unbounded => K::Int::MAX,
        };
        let raw = Self::raw_cursor_at(self, key);
        CursorMut { raw }
    }
}
