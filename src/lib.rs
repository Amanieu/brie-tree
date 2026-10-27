//! This crate provides [`BTree`], a fast B+ Tree implementation using integer
//! keys.

#![cfg_attr(not(any(test, feature = "internal_benches")), no_std)]
#![warn(missing_docs)]

use core::mem;

use allocator_api2::alloc::{Allocator, Global};
use int::BTreeInteger;
use node::{NodePool, NodeRef, UninitNodeRef};
use stack::Height;

#[macro_use]
mod node;

mod append;
mod cursor;
mod int;
mod iter;
mod simd;
mod stack;
#[cfg(test)]
mod tests;

pub use cursor::*;
pub use iter::*;

use crate::int::int_from_key;

/// Trait which must be implemented for all keys inserted into a [`BTree`].
///
/// This trait is implemented for fixed-width primitive integers.
///
/// Custom key types can implement it by converting to and from an integer.
///
/// Note that keys in the [`BTree`] are ordered by their integer value and not
/// the [`Ord`] implementation of the key type.
pub trait BTreeKey: Copy {
    /// Integer representation of this key.
    ///
    /// This must be `u8`, `u16`, `u32`, `u64`, `u128`, `i8`, `i16`, `i32`,
    /// `i64`, or `i128`.
    #[allow(private_bounds)]
    type Int: BTreeInteger;

    /// Converts the key to an integer.
    fn to_int(self) -> Self::Int;

    /// Recovers the key from an integer.
    fn from_int(int: Self::Int) -> Self;
}

/// An ordered multi-map based on a [B+ Tree].
///
/// This is similar to the standard library's `BTreeMap` but differs in several
/// ways:
/// - Lookups and insertions are 2-4x faster than `BTreeMap`.
/// - `BTree` holds duplicate keys: insertion never replaces existing entries.
/// - Keys must be `Copy` and convertible to and from integers via the
///   [`BTreeKey`] trait.
/// - Elements in the tree are ordered by the integer value of the key instead
///   of the [`Ord`] implementation of the keys.
/// - [`Cursor`] and [`CursorMut`] can be used to seek back-and-forth in the
///   tree while inserting or removing elements.
/// - Iterators only support forward iteration.
///
/// [`BTree::get`], [`BTree::get_mut`] and [`BTree::remove`] operate on only one
/// entry with the given key (arbitrarily chosen). Use [`BTree::range`] or
/// [`BTree::cursor_mut_at`] to access all entries with a given key.
///
/// The data structure design is based on the [B- Tree] by Sergey Slotin, but
/// has been significantly extended.
///
/// [B+ Tree]: https://en.wikipedia.org/wiki/B%2B_tree
/// [B- Tree]: https://en.algorithmica.org/hpc/data-structures/b-tree/
pub struct BTree<K: BTreeKey, V, A: Allocator = Global> {
    internal: NodePool<K::Int, NodeRef>,
    leaf: NodePool<K::Int, V>,
    height: Height<K::Int>,
    root: NodeRef,
    alloc: A,
}

impl<K: BTreeKey, V> BTree<K, V, Global> {
    /// Creates a new, empty [`BTree`].
    ///
    /// This requires an initial memory allocation on creation.
    #[inline]
    pub fn new() -> Self {
        Self::new_in(Global)
    }

    /// Creates a new [`BTree`] from sorted entries, preserving duplicate keys
    /// and their input order.
    ///
    /// Keys must be in nondecreasing order by their integer values. Violating
    /// this invariant is safe but may cause other operations to return
    /// incorrect results or panic.
    ///
    /// Uses [`BTree::append_sorted`] to build the tree efficiently.
    #[inline]
    pub fn from_sorted_iter(iter: impl IntoIterator<Item = (K, V)>) -> Self {
        Self::from_sorted_iter_in(iter, Global)
    }
}

impl<K: BTreeKey, V, A: Allocator> BTree<K, V, A> {
    /// Creates a new, empty [`BTree`] with the given allocator.
    ///
    /// This requires an initial memory allocation on creation.
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        let mut out = Self {
            internal: NodePool::new(),
            leaf: NodePool::new(),
            height: Height::leaf(),
            root: NodeRef::zero(),
            alloc,
        };
        let root = unsafe { out.leaf.alloc_node(&out.alloc) };
        out.init_root(root);
        out
    }

    /// Creates a new [`BTree`] from sorted entries with the given allocator,
    /// preserving duplicate keys and their input order.
    ///
    /// Keys must be in nondecreasing order by their integer values. Violating
    /// this invariant is safe but may cause other operations to return
    /// incorrect results or panic.
    ///
    /// Uses [`BTree::append_sorted`] to build the tree efficiently.
    #[inline]
    pub fn from_sorted_iter_in(iter: impl IntoIterator<Item = (K, V)>, alloc: A) -> Self {
        let mut tree = Self::new_in(alloc);
        tree.append_sorted(iter);
        tree
    }

    /// Initializes the root node to the leaf node at offset zero.
    #[inline]
    fn init_root(&mut self, root: UninitNodeRef) {
        let root = unsafe { root.init_keys(&mut self.leaf) };
        unsafe { root.set_metadata(pos!(0), NodeRef::INVALID, &mut self.leaf) };
        debug_assert_eq!(root, NodeRef::zero());
        self.root = NodeRef::zero();
    }

    /// Adds a root whose children are the old root and `right`, returning it.
    ///
    /// # Safety
    ///
    /// The old root and `right` must be disjoint, initialized subtrees of the
    /// current height, allocated from this tree's pools. `left_max` must be the
    /// old root's rightmost leaf key. Leaf links must already connect the two
    /// subtrees. Underfull nodes are permitted during bulk loading, but the
    /// caller must restore their occupancy before exposing the tree.
    #[inline]
    unsafe fn push_root(
        &mut self,
        left_max: <K::Int as BTreeInteger>::Raw,
        right: NodeRef,
    ) -> NodeRef {
        let new_uninit_root = unsafe { self.internal.alloc_node(&self.alloc) };

        // The new root only contains 2 elements: the original root node and the
        // new right node. The first key holds the maximum key in the
        // left sub-tree; the second key stays MAX.
        let new_root;
        unsafe {
            new_root = new_uninit_root.init_keys(&mut self.internal);
            new_root.set_key(left_max, pos!(0), &mut self.internal);
            new_root
                .value_mut(pos!(0), &mut self.internal)
                .write(self.root);
            new_root.value_mut(pos!(1), &mut self.internal).write(right);
            new_root.set_end_internal(pos!(2), &mut self.internal);
        }
        self.root = new_root;

        // Increment the height of the tree. The `expect` should never fail here
        // since we calculated the maximum possible height for the tree
        // statically as `Height::max`.
        self.height = self
            .height
            .up(Height::max())
            .expect("exceeded maximum height");
        new_root
    }

    /// Clears the map, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        struct ClearGuard<'a, K: BTreeKey, V, A: Allocator> {
            btree: &'a mut BTree<K, V, A>,
        }

        impl<K: BTreeKey, V, A: Allocator> Drop for ClearGuard<'_, K, V, A> {
            #[inline]
            fn drop(&mut self) {
                // Free all nodes without freeing the underlying allocations.
                let root = self.btree.leaf.clear_and_alloc_node();
                self.btree.internal.clear();

                // Re-initialize the root node.
                self.btree.height = Height::leaf();
                self.btree.init_root(root);
            }
        }

        // Ensure the tree is left empty even if dropping a value panics.
        let guard = ClearGuard { btree: self };

        // Drop values. We don't need to modify the keys since we're about to
        // free the nodes afterwards.
        if mem::needs_drop::<V>() {
            let mut iter = guard.btree.raw_iter();
            while let Some((_key, value_ptr)) = unsafe { iter.next(&guard.btree.leaf) } {
                unsafe {
                    value_ptr.drop_in_place();
                }
            }
        }
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        // The first leaf always has offset zero and is never deleted. It is
        // empty exactly when the tree is empty.
        unsafe { NodeRef::zero().end(&self.leaf) == pos!(0) }
    }

    /// Returns a reference to one value associated with the key, or `None` if
    /// the key is absent.
    ///
    /// If multiple entries have this key, one is arbitrarily chosen.
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        self.range(key..=key).next().map(|(_k, v)| v)
    }

    /// Returns a mutable reference to one value associated with the key, or
    /// `None` if the key is absent.
    ///
    /// If multiple entries have this key, one is arbitrarily chosen.
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.range_mut(key..=key).next().map(|(_k, v)| v)
    }

    /// Inserts a key-value pair into the multi-map.
    ///
    /// Existing entries with the same key are not replaced.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let mut cursor = unsafe { CursorMut::uninit(self) };
        cursor.seek(int_from_key(key));
        cursor.insert_before(key, value);
    }

    /// Removes one entry with the given key, returning its value, or `None` if
    /// the key is absent.
    ///
    /// If multiple entries have this key, one is arbitrarily chosen. Other
    /// entries with the same key remain in the tree.
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<V> {
        let mut cursor = unsafe { CursorMut::uninit(self) };
        cursor.seek(int_from_key(key));
        if cursor.key()?.to_int() == key.to_int() {
            return Some(cursor.remove().1);
        }
        None
    }
}

impl<K: BTreeKey, V, A: Allocator> Drop for BTree<K, V, A> {
    #[inline]
    fn drop(&mut self) {
        struct DropGuard<'a, K: BTreeKey, V, A: Allocator> {
            btree: &'a mut BTree<K, V, A>,
        }

        impl<K: BTreeKey, V, A: Allocator> Drop for DropGuard<'_, K, V, A> {
            #[inline]
            fn drop(&mut self) {
                unsafe {
                    self.btree.internal.clear_and_free(&self.btree.alloc);
                    self.btree.leaf.clear_and_free(&self.btree.alloc);
                }
            }
        }

        // Release the pools even if a value destructor panics. Unvisited values
        // are discarded without running their destructors in that case.
        let guard = DropGuard { btree: self };

        // Drop values. We don't need to modify the keys since we're about to
        // free the nodes anyways.
        if mem::needs_drop::<V>() {
            let mut iter = guard.btree.raw_iter();
            while let Some((_key, value_ptr)) = unsafe { iter.next(&guard.btree.leaf) } {
                unsafe {
                    value_ptr.drop_in_place();
                }
            }
        }
    }
}

impl<K: BTreeKey, V, A: Default + Allocator> Default for BTree<K, V, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(Default::default())
    }
}

impl<K: BTreeKey, V> FromIterator<(K, V)> for BTree<K, V> {
    /// Creates a multi-map containing every input entry, including duplicate keys.
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut btree = BTree::new();
        btree.extend(iter);
        btree
    }
}

impl<K: BTreeKey, V, A: Allocator> Extend<(K, V)> for BTree<K, V, A> {
    /// Inserts every input entry, including duplicate keys, without replacing
    /// any existing entries.
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<K: BTreeKey, V: Clone, A: Allocator + Clone> Clone for BTree<K, V, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self::from_sorted_iter_in(
            self.iter().map(|(key, value)| (key, value.clone())),
            self.alloc.clone(),
        )
    }
}

impl<'a, K: BTreeKey, V: Clone, A: Allocator> Extend<(K, &'a V)> for BTree<K, V, A> {
    /// Clones each input value and inserts every entry, including duplicate
    /// keys, without replacing any existing entries.
    #[inline]
    fn extend<T: IntoIterator<Item = (K, &'a V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(k, v)| {
            self.insert(k, v.clone());
        });
    }
}
