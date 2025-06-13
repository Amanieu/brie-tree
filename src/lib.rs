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

mod cursor;
mod int;
mod iter;
mod simd;
mod stack;
#[cfg(test)]
mod tests;

pub use nonmax;

pub use cursor::*;
pub use iter::*;

use crate::int::int_from_key;

/// Trait which must be implemented for all keys inserted into a [`BTree`].
///
/// [`BTree`] requires that keys be integers and reserves the maximum integer
/// value for internal use. This trait is already implementated for all integers
/// from the [`nonmax`] crate, but this crate allows for custom key types that
/// are convertible to/from an integer.
///
/// Note that keys in the [`BTree`] are ordered by their integer value and not
/// the [`Ord`] implementation of the key type.
pub trait BTreeKey: Copy {
    /// Non-max integer type that this key
    ///
    /// This must be one of the integer types from the [`nonmax`] crate:
    /// - [`nonmax::NonMaxU8`]
    /// - [`nonmax::NonMaxU16`]
    /// - [`nonmax::NonMaxU32`]
    /// - [`nonmax::NonMaxU64`]
    /// - [`nonmax::NonMaxU128`]
    /// - [`nonmax::NonMaxI8`]
    /// - [`nonmax::NonMaxI16`]
    /// - [`nonmax::NonMaxI32`]
    /// - [`nonmax::NonMaxI64`]
    /// - [`nonmax::NonMaxI128`]
    #[allow(private_bounds)]
    type Int: BTreeInteger;

    /// Converts the key to an integer.
    fn to_int(self) -> Self::Int;

    /// Recovers the key from an integer.
    fn from_int(int: Self::Int) -> Self;
}

/// An ordered map based on a [B+ Tree].
///
/// This is similar to the standard library's `BTreeMap` but differs in several
/// ways:
/// - Lookups and insertions are 2-4x faster than `BTreeMap`.
/// - `BTree` can optionally be used as a multi-map and hold duplicate keys.
/// - Keys must be `Copy` and convertible to and from integers via the
///   [`BTreeKey`] trait.
/// - The maximum integer value is reserved for internal use and cannot be used
///   by keys.
/// - Elements in the tree are ordered by the integer value of the key instead
///   of the [`Ord`] implementation of the keys.
/// - [`Cursor`] and [`CursorMut`] can be used to seek back-and-forth in the
///   tree while inserting or removing elements.
/// - Iterators only support forward iteration.
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

    /// Initializes the root node to the leaf node at offset zero.
    #[inline]
    fn init_root(&mut self, root: UninitNodeRef) {
        let root = unsafe { root.init_keys(&mut self.leaf) };
        unsafe {
            root.set_next_leaf(None, &mut self.leaf);
        }
        debug_assert_eq!(root, NodeRef::zero());
        self.root = NodeRef::zero();
    }

    /// Clears the map, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        // Drop values. We don't need to modify the keys since we're about to
        // free the nodes anyways.
        if mem::needs_drop::<V>() {
            let mut iter = self.raw_iter();
            while let Some((_key, value_ptr)) = unsafe { iter.next(&self.leaf) } {
                unsafe {
                    value_ptr.drop_in_place();
                }
            }
        }

        // Free all nodes without freeing the underlying allocations.
        let root = self.leaf.clear_and_alloc_node();
        self.internal.clear();

        // Re-initialize the root node.
        self.height = Height::leaf();
        self.init_root(root);
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        if self.height != Height::leaf() {
            return false;
        }
        let first_key = unsafe { self.root.key(pos!(0), &self.leaf) };
        first_key == K::Int::MAX
    }

    /// Returns a reference to the value corresponding to the key.
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        self.range(key..=key).next().map(|(_k, v)| v)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.range_mut(key..=key).next().map(|(_k, v)| v)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut cursor = unsafe { CursorMut::uninit(self) };
        cursor.seek(int_from_key(key));
        if let Some((k, v)) = cursor.entry_mut()
            && k.to_int() == key.to_int()
        {
            return Some(mem::replace(v, value));
        }
        cursor.insert_before(key, value);
        None
    }

    /// Inserts a key-value pair into the map while allowing for multiple
    /// identical keys.
    ///
    /// This allows the `BTree` to be used as a multi-map where each key can
    /// have multiple values. In this case [`BTree::get`], [`BTree::get_mut`]
    /// and [`BTree::remove`] will only operate on one of the associated values
    /// (arbitrarily chosen).
    #[inline]
    pub fn insert_multi(&mut self, key: K, value: V) {
        let mut cursor = unsafe { CursorMut::uninit(self) };
        cursor.seek(int_from_key(key));
        cursor.insert_before(key, value);
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
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
        // Drop values. We don't need to modify the keys since we're about to
        // free the nodes anyways.
        if mem::needs_drop::<V>() {
            let mut iter = self.raw_iter();
            while let Some((_key, value_ptr)) = unsafe { iter.next(&self.leaf) } {
                unsafe {
                    value_ptr.drop_in_place();
                }
            }
        }

        // Release all allocated memory
        unsafe {
            self.internal.clear_and_free(&self.alloc);
            self.leaf.clear_and_free(&self.alloc);
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
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut btree = BTree::new();
        btree.extend(iter);
        btree
    }
}

impl<K: BTreeKey, V, A: Allocator> Extend<(K, V)> for BTree<K, V, A> {
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
        let mut btree = BTree::new_in(self.alloc.clone());
        btree.extend(self.iter());
        btree
    }
}

impl<'a, K: BTreeKey, V: Clone, A: Allocator> Extend<(K, &'a V)> for BTree<K, V, A> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, &'a V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(k, v)| {
            self.insert(k, v.clone());
        });
    }
}
