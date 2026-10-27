//! Bulk loading sorted entries along the right edge of a tree.
//!
//! Unlike ordinary insertion, a full node is left intact and a new sibling
//! starts with just one entry. Only nodes on the right edge may be underfull.
//! Once loading ends, including on unwind, entries from full left siblings
//! restore the minimum occupancy without splitting or merging nodes.

use allocator_api2::alloc::Allocator;

use crate::{
    BTree, BTreeKey,
    int::{BTreeInteger, int_from_key},
    node::{NodePool, NodePos, NodeRef},
    stack::Height,
};

impl<K: BTreeKey, V, A: Allocator> BTree<K, V, A> {
    /// Appends every entry from a sorted iterator without replacing existing
    /// entries.
    ///
    /// This is more efficient than repeated insertion because it fills new
    /// nodes densely and avoids searching for each insertion position.
    ///
    /// Keys must be in nondecreasing order and must be at least the greatest
    /// key already in the tree.
    ///
    /// It is the user's responsibility to ensure that appending these entries
    /// does not violate the invariant that all keys must be in sorted order
    /// in the tree. Violating this invariant is safe but may cause other
    /// operations to return incorrect results or panic.
    pub fn append_sorted(&mut self, iter: impl IntoIterator<Item = (K, V)>) {
        struct AppendGuard<'a, K: BTreeKey, V, A: Allocator> {
            btree: &'a mut BTree<K, V, A>,
            // The leaf position tracks its initialized length. Its metadata
            // may be stale or uninitialized until rollover or guard cleanup.
            stack: <K::Int as BTreeInteger>::Stack,
        }

        impl<K: BTreeKey, V, A: Allocator> Drop for AppendGuard<'_, K, V, A> {
            fn drop(&mut self) {
                let tree = &mut self.btree;

                // Update the active leaf's length. This is deferred until the
                // end to avoid redundant writes.
                let (leaf, end) = self.stack[Height::leaf()];
                unsafe { leaf.set_metadata(end, NodeRef::INVALID, &mut tree.leaf) };

                // The bulk append may have left nodes on the right edge of the
                // tree with less than B/2 elements, which violates the tree
                // invariant. Run a fixup pass which rebalances those with their
                // sibling.
                //
                // There is nothing to do if this is a single-level tree since
                // the invariant doesn't apply to the root node.
                let mut node = tree.root;
                let mut height = tree.height;
                while let Some(down) = height.down() {
                    unsafe {
                        // An internal root has at least two children, and other
                        // parents have already been repaired by the previous
                        // iteration.
                        let last = node.end_internal(&tree.internal).prev();
                        let child = node.value(last, &tree.internal).assume_init_read();
                        let child_end = if down == Height::leaf() {
                            child.end(&tree.leaf)
                        } else {
                            child.end_internal(&tree.internal)
                        };

                        // A sufficiently full child needs no repair.
                        if child_end >= pos!(K::Int::B / 2) {
                            node = child;
                            height = down;
                            continue;
                        }

                        // The child's left sibling is guaranteed to be full:
                        // an underfull node could only have been produced by
                        // append_sorted if the previous node was full.
                        let sibling_pos = last.prev();
                        let sibling = node.value(sibling_pos, &tree.internal).assume_init_read();
                        let separator = node.key(sibling_pos, &tree.internal);
                        let new_separator = if down == Height::leaf() {
                            rebalance_siblings(
                                sibling,
                                child,
                                child_end.index(),
                                separator,
                                true,
                                &mut tree.leaf,
                            )
                        } else {
                            rebalance_siblings(
                                sibling,
                                child,
                                child_end.index(),
                                separator,
                                false,
                                &mut tree.internal,
                            )
                        };

                        // Redistribution changes the left subtree's maximum,
                        // but the rightmost child's key remains MAX.
                        node.set_key(new_separator, sibling_pos, &mut tree.internal);
                        node = child;
                    }
                    height = down;
                }
            }
        }

        /// Redistributes entries from a full left sibling to an underfull right
        /// sibling, returning the left sibling's new maximum key for the
        /// parent. `separator` is the left subtree's current maximum; `leaf`
        /// indicates whether these are leaf nodes.
        ///
        /// # Safety
        ///
        /// The nodes must be distinct and initialized in `pool`, with `I::B -
        /// 1` live entries in `left` and `right_len` in `right`. `right_len`
        /// must be in `1..I::B / 2`.
        unsafe fn rebalance_siblings<I: BTreeInteger, V>(
            left: NodeRef,
            right: NodeRef,
            right_len: usize,
            separator: I::Raw,
            leaf: bool,
            pool: &mut NodePool<I, V>,
        ) -> I::Raw {
            unsafe {
                debug_assert!(right_len < I::B / 2);
                debug_assert_eq!(left.end(pool).index(), I::B - 1);

                // Move the full left node's last B / 2 - 1 entries to the
                // front of the right node. This leaves B / 2 entries on the
                // left and between B / 2 and B - 2 entries on the right.
                let transfer_count = I::B / 2 - 1;
                let new_left_end = NodePos::new_unchecked(I::B / 2);
                if !leaf {
                    // An internal node's last child has a MAX key instead of
                    // its actual maximum. This child will no longer be last
                    // after moving to the right node, so give it its actual
                    // maximum, currently stored in the parent as separator.
                    left.set_key(separator, NodePos::new_unchecked(I::B - 2), pool);
                }
                left.transfer_suffix_to(right, new_left_end, transfer_count, pool);
                left.set_end(new_left_end, pool);
                right.set_end(NodePos::new_unchecked(right_len + transfer_count), pool);

                // The last remaining entry gives the left subtree's new
                // maximum. Return it for the parent; for an internal node,
                // replace it with MAX now that this child is last.
                let new_separator = left.key(new_left_end.prev(), pool);
                if !leaf {
                    left.set_key(I::MAX, new_left_end.prev(), pool);
                }
                new_separator
            }
        }

        // Initialize the stack with the path to the end of the rightmost leaf.
        let mut stack = <K::Int as BTreeInteger>::Stack::default();
        let mut height = self.height;
        let mut node = self.root;
        while let Some(down) = height.down() {
            unsafe {
                let last = node.end_internal(&self.internal).prev();
                stack[height] = (node, last);
                node = node.value(last, &self.internal).assume_init_read();
            }
            height = down;
        }
        stack[Height::leaf()] = (node, unsafe { node.end(&self.leaf) });

        // Install a guard to ensure we restore the tree invariants, even on
        // unwind.
        let mut guard = AppendGuard { btree: self, stack };

        for (key, value) in iter {
            // Convert before mutating the tree: this is the only statement in
            // this loop that can unwind.
            let key = int_from_key(key);

            unsafe {
                let (leaf, end) = guard.stack[Height::leaf()];

                // Fast path: if the node isn't full then just append to it.
                if end != pos!(K::Int::B - 1) {
                    leaf.set_key(key, end, &mut guard.btree.leaf);
                    leaf.value_mut(end, &mut guard.btree.leaf).write(value);
                    guard.stack[Height::leaf()].1 = end.next();
                    continue;
                }

                // Save the full leaf's last key for the parent separator when
                // we attach the new right sibling.
                let left_max = leaf.key(pos!(K::Int::B - 2), &guard.btree.leaf);

                // Allocate a new leaf and store the new entry in it.
                let new = guard.btree.leaf.alloc_node(&guard.btree.alloc);
                let new = new.init_keys(&mut guard.btree.leaf);
                new.set_key(key, pos!(0), &mut guard.btree.leaf);
                new.value_mut(pos!(0), &mut guard.btree.leaf).write(value);

                // Finalize the metadata of the old leaf and link it to the new
                // one.
                leaf.set_metadata(end, new, &mut guard.btree.leaf);
                guard.stack[Height::leaf()] = (new, pos!(1));

                // Attach the new node to its parent in the level above. This
                // may recursively create new nodes in that level.
                let mut child = new;
                let mut height = Height::leaf();
                loop {
                    if let Some(up) = height.up(guard.btree.height) {
                        height = up;
                        let (parent, last) = guard.stack[height];
                        let end = last.next();

                        // Fast path: if the node isn't full then just append to
                        // it.
                        if end != pos!(K::Int::B - 1) {
                            // Update the maximum key of the old subtree. It was
                            // previously MAX since this was the last subtree.
                            debug_assert_eq!(parent.key(last, &guard.btree.internal), K::Int::MAX);
                            parent.set_key(left_max, last, &mut guard.btree.internal);
                            parent
                                .value_mut(end, &mut guard.btree.internal)
                                .write(child);
                            parent.set_end_internal(end.next(), &mut guard.btree.internal);
                            guard.stack[height].1 = end;
                            break;
                        }

                        // This parent is full. Start its right sibling with
                        // the new child and let the next level attach it.
                        let new = guard.btree.internal.alloc_node(&guard.btree.alloc);
                        let new = new.init_keys(&mut guard.btree.internal);
                        new.value_mut(pos!(0), &mut guard.btree.internal)
                            .write(child);
                        new.set_end_internal(pos!(1), &mut guard.btree.internal);
                        guard.stack[height] = (new, pos!(0));
                        child = new;
                    } else {
                        // If we reached the root of the tree then we need to
                        // add a new level to the tree and create a new root
                        // node.
                        let new = guard.btree.push_root(left_max, child);
                        guard.stack[guard.btree.height] = (new, pos!(1));
                        break;
                    }
                }
            }
        }
    }
}
