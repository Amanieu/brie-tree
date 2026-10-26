use core::{
    hint,
    iter::FusedIterator,
    mem::{self, ManuallyDrop},
    ops::{Bound, RangeBounds},
    ptr::{self, NonNull},
};

use allocator_api2::alloc::{Allocator, Global};

use crate::{
    BTree, BTreeKey,
    int::{BTreeInteger, int_from_key},
    node::{NodePool, NodePos, NodeRef},
};

/// Common base for mutable and immutable iterators.
#[derive(Clone)]
pub(crate) struct RawIter<I: BTreeInteger> {
    /// Current leaf node, or `NodeRef::INVALID` if the iterator is exhausted.
    node: NodeRef,

    /// Current position in the node.
    ///
    /// This must point to a live entry when `node` is valid, and is ignored
    /// when the iterator is exhausted.
    pos: NodePos<I>,
}

impl<I: BTreeInteger> RawIter<I> {
    /// Creates an exhausted iterator.
    #[inline]
    fn empty() -> Self {
        Self {
            node: NodeRef::INVALID,
            pos: NodePos::zero(),
        }
    }

    /// Creates an iterator from a leaf position obtained by a lookup.
    ///
    /// # Safety
    ///
    /// `node` must be an initialized leaf in `leaf_pool`.
    /// `pos` must point to a live entry or the first unused slot.
    #[inline]
    pub(crate) unsafe fn new<V>(
        node: NodeRef,
        pos: NodePos<I>,
        leaf_pool: &NodePool<I, V>,
    ) -> Self {
        // Allocated nodes cannot be the sentinel. Expose this to the optimizer
        // so an immediate next() need not check the input node again.
        unsafe { hint::assert_unchecked(node != NodeRef::INVALID) };

        let mut iter = Self { node, pos };
        // A lookup may point to the first unused slot instead of a live MAX key.
        if unsafe { iter.is_leaf_end(leaf_pool) } {
            iter.node = NodeRef::INVALID;
        }
        iter
    }

    /// Tests whether the position is the first unused slot, checking length
    /// only for MAX.
    ///
    /// # Safety
    ///
    /// `self.node` must be an initialized leaf in `leaf_pool`.
    /// `self.pos` must point to a live entry or the first unused slot.
    #[inline]
    unsafe fn is_leaf_end<V>(&self, leaf_pool: &NodePool<I, V>) -> bool {
        debug_assert!(self.pos <= unsafe { self.node.end(leaf_pool) });
        unsafe {
            self.node.key(self.pos, leaf_pool) == I::MAX && self.pos == self.node.end(leaf_pool)
        }
    }

    /// Returns the next key that the iterator will yield, or `None` if it is
    /// at the end of the tree.
    ///
    /// # Safety
    ///
    /// `leaf_pool` must point to the `NodePool` for leaf nodes in the tree.
    #[inline]
    unsafe fn next_key<V>(&self, leaf_pool: &NodePool<I, V>) -> Option<I::Raw> {
        if self.node == NodeRef::INVALID {
            return None;
        }
        Some(unsafe { self.node.key(self.pos, leaf_pool) })
    }

    /// Advances the iterator to the next element in the tree.
    ///
    /// # Safety
    ///
    /// `leaf_pool` must point to the `NodePool` for leaf nodes in the tree.
    #[inline]
    pub(crate) unsafe fn next<V>(&mut self, leaf_pool: &NodePool<I, V>) -> Option<(I, NonNull<V>)> {
        // Get the current element that will be returned.
        let key = I::from_raw(unsafe { self.next_key(leaf_pool) }?);
        let value = unsafe { self.node.values_ptr(leaf_pool).add(self.pos.index()) };

        // First, try to move to the next element in the current leaf.
        self.pos = unsafe { self.pos.next() };

        // If we reached the end of the leaf then we need to advance to the next
        // leaf node, or the sentinel if this was the last leaf.
        if unsafe { self.is_leaf_end(leaf_pool) } {
            self.node = unsafe { self.node.next_leaf(leaf_pool) };
            // A successor leaf cannot be the root, so it is at least half full
            // and position zero is live unless we reached the sentinel.
            debug_assert!(
                self.node == NodeRef::INVALID
                    || unsafe { self.node.end(leaf_pool).index() >= I::B / 2 }
            );
            self.pos = NodePos::zero();
        }

        Some((key, value.cast()))
    }
}

/// An iterator over the entries of a [`BTree`].
pub struct Iter<'a, K: BTreeKey, V, A: Allocator = Global> {
    pub(crate) raw: RawIter<K::Int>,
    pub(crate) btree: &'a BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for Iter<'a, K, V, A> {
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(key, value_ptr)| (K::from_int(key), value_ptr.as_ref()))
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for Iter<'a, K, V, A> {}

impl<'a, K: BTreeKey, V, A: Allocator> Clone for Iter<'a, K, V, A> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            btree: self.btree,
        }
    }
}

/// A mutable iterator over the entries of a [`BTree`].
pub struct IterMut<'a, K: BTreeKey, V, A: Allocator = Global> {
    pub(crate) raw: RawIter<K::Int>,
    pub(crate) btree: &'a mut BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for IterMut<'a, K, V, A> {
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(key, mut value_ptr)| (K::from_int(key), value_ptr.as_mut()))
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for IterMut<'a, K, V, A> {}

/// An owning iterator over the entries of a [`BTree`].
pub struct IntoIter<K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    btree: ManuallyDrop<BTree<K, V, A>>,
}

impl<K: BTreeKey, V, A: Allocator> Iterator for IntoIter<K, V, A> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Read the element out of the tree without touching the key.
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(key, value_ptr)| (K::from_int(key), value_ptr.read()))
        }
    }
}

impl<K: BTreeKey, V, A: Allocator> Drop for IntoIter<K, V, A> {
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
                    ptr::drop_in_place(&mut self.btree.alloc);
                }
            }
        }

        // Release the pools and allocator even if a value destructor panics.
        // Unvisited values are discarded without running their destructors.
        let guard = DropGuard {
            btree: &mut self.btree,
        };

        // Ensure all remaining elements are dropped.
        if mem::needs_drop::<V>() {
            while let Some((_key, value_ptr)) = unsafe { self.raw.next(&guard.btree.leaf) } {
                unsafe {
                    value_ptr.drop_in_place();
                }
            }
        }
    }
}

impl<K: BTreeKey, V, A: Allocator> FusedIterator for IntoIter<K, V, A> {}

/// An iterator over the keys of a [`BTree`].
pub struct Keys<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    btree: &'a BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for Keys<'a, K, V, A> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(key, _value_ptr)| K::from_int(key))
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for Keys<'a, K, V, A> {}

impl<'a, K: BTreeKey, V, A: Allocator> Clone for Keys<'a, K, V, A> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            btree: self.btree,
        }
    }
}

/// An iterator over the values of a [`BTree`].
pub struct Values<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    btree: &'a BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for Values<'a, K, V, A> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(_key, value_ptr)| value_ptr.as_ref())
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for Values<'a, K, V, A> {}

impl<'a, K: BTreeKey, V, A: Allocator> Clone for Values<'a, K, V, A> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            btree: self.btree,
        }
    }
}

/// A mutable iterator over the values of a [`BTree`].
pub struct ValuesMut<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    btree: &'a mut BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for ValuesMut<'a, K, V, A> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.raw
                .next(&self.btree.leaf)
                .map(|(_key, mut value_ptr)| value_ptr.as_mut())
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for ValuesMut<'a, K, V, A> {}

/// An iterator over a sub-range of the entries of a [`BTree`].
pub struct Range<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    inclusive_end: <K::Int as BTreeInteger>::Raw,
    btree: &'a BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for Range<'a, K, V, A> {
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let key = self.raw.next_key(&self.btree.leaf)?;
            if K::Int::cmp(key, self.inclusive_end).is_gt() {
                return None;
            }

            self.raw
                .next(&self.btree.leaf)
                .map(|(key, value_ptr)| (K::from_int(key), value_ptr.as_ref()))
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for Range<'a, K, V, A> {}

impl<'a, K: BTreeKey, V, A: Allocator> Clone for Range<'a, K, V, A> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            inclusive_end: self.inclusive_end,
            btree: self.btree,
        }
    }
}

/// A mutable iterator over a sub-range of the entries of a [`BTree`].
pub struct RangeMut<'a, K: BTreeKey, V, A: Allocator = Global> {
    raw: RawIter<K::Int>,
    inclusive_end: <K::Int as BTreeInteger>::Raw,
    btree: &'a mut BTree<K, V, A>,
}

impl<'a, K: BTreeKey, V, A: Allocator> Iterator for RangeMut<'a, K, V, A> {
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let key = self.raw.next_key(&self.btree.leaf)?;
            if K::Int::cmp(key, self.inclusive_end).is_gt() {
                return None;
            }

            self.raw
                .next(&self.btree.leaf)
                .map(|(key, mut value_ptr)| (K::from_int(key), value_ptr.as_mut()))
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> FusedIterator for RangeMut<'a, K, V, A> {}

impl<K: BTreeKey, V, A: Allocator> BTree<K, V, A> {
    /// Returns a [`RawIter`] pointing at the first element of the tree.
    #[inline]
    pub(crate) fn raw_iter(&self) -> RawIter<K::Int> {
        // The first leaf node is always the left-most leaf on the tree and is
        // never deleted.
        let node = NodeRef::zero();
        let pos = pos!(0);
        unsafe { RawIter::new(node, pos, &self.leaf) }
    }

    /// Returns a [`RawIter`] pointing at the first element with key greater
    /// than or equal to `key`.
    #[inline]
    pub(crate) fn raw_iter_from(
        &self,
        key: Option<<K::Int as BTreeInteger>::Raw>,
    ) -> RawIter<K::Int> {
        // An excluded MAX bound is past the end of the tree.
        let Some(key) = key else {
            return RawIter::empty();
        };

        // Go down the tree, at each internal node selecting the first sub-tree
        // with key greater than or equal to the search key. This sub-tree will
        // only contain keys less than or equal to its key.
        let mut height = self.height;
        let mut node = self.root;
        while let Some(down) = height.down() {
            let keys = unsafe { node.keys(&self.internal) };
            let pos = unsafe { K::Int::search(keys, key) };
            node = unsafe { node.value(pos, &self.internal).assume_init_read() };
            height = down;
        }

        // Select the first leaf element with key greater than or equal to the
        // search key.
        let keys = unsafe { node.keys(&self.leaf) };
        let pos = unsafe { K::Int::search(keys, key) };
        unsafe { RawIter::new(node, pos, &self.leaf) }
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V, A> {
        Iter {
            raw: self.raw_iter(),
            btree: self,
        }
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, A> {
        IterMut {
            raw: self.raw_iter(),
            btree: self,
        }
    }

    /// Gets an iterator over the entries of the map starting from the given
    /// bound.
    #[inline]
    pub fn iter_from(&self, bound: Bound<K>) -> Iter<'_, K, V, A> {
        let raw = match bound {
            Bound::Included(key) => self.raw_iter_from(Some(int_from_key(key))),
            Bound::Excluded(key) => self.raw_iter_from(K::Int::increment(int_from_key(key))),
            Bound::Unbounded => self.raw_iter(),
        };
        Iter { raw, btree: self }
    }

    /// Gets a mutable iterator over the entries of the map starting from the
    /// given bound.
    #[inline]
    pub fn iter_mut_from(&mut self, bound: Bound<K>) -> IterMut<'_, K, V, A> {
        let raw = match bound {
            Bound::Included(key) => self.raw_iter_from(Some(int_from_key(key))),
            Bound::Excluded(key) => self.raw_iter_from(K::Int::increment(int_from_key(key))),
            Bound::Unbounded => self.raw_iter(),
        };
        IterMut { raw, btree: self }
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V, A> {
        Keys {
            raw: self.raw_iter(),
            btree: self,
        }
    }

    /// Gets an iterator over the values of the map, in order by key.
    #[inline]
    pub fn values(&self) -> Values<'_, K, V, A> {
        Values {
            raw: self.raw_iter(),
            btree: self,
        }
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, A> {
        ValuesMut {
            raw: self.raw_iter(),
            btree: self,
        }
    }

    /// Constructs an iterator over a sub-range of elements in the map.
    ///
    /// Unlike `BTreeMap`, this is not a [`DoubleEndedIterator`]: it only allows
    /// forward iteration.
    #[inline]
    pub fn range(&self, range: impl RangeBounds<K>) -> Range<'_, K, V, A> {
        let mut raw = match range.start_bound() {
            Bound::Included(&key) => self.raw_iter_from(Some(int_from_key(key))),
            Bound::Excluded(&key) => self.raw_iter_from(K::Int::increment(int_from_key(key))),
            Bound::Unbounded => self.raw_iter(),
        };
        let inclusive_end = match range.end_bound() {
            Bound::Included(&key) => int_from_key(key),
            Bound::Excluded(&key) => {
                let inclusive_end = K::Int::wrapping_decrement(int_from_key(key));
                if inclusive_end == K::Int::MAX {
                    // No key is below MIN, so the range is empty.
                    raw.node = NodeRef::INVALID;
                }
                inclusive_end
            }
            Bound::Unbounded => K::Int::MAX,
        };
        Range {
            raw,
            inclusive_end,
            btree: self,
        }
    }

    /// Constructs a mutable iterator over a sub-range of elements in the map.
    ///
    /// Unlike `BTreeMap`, this is not a [`DoubleEndedIterator`]: it only allows
    /// forward iteration.
    #[inline]
    pub fn range_mut(&mut self, range: impl RangeBounds<K>) -> RangeMut<'_, K, V, A> {
        let mut raw = match range.start_bound() {
            Bound::Included(&key) => self.raw_iter_from(Some(int_from_key(key))),
            Bound::Excluded(&key) => self.raw_iter_from(K::Int::increment(int_from_key(key))),
            Bound::Unbounded => self.raw_iter(),
        };
        let inclusive_end = match range.end_bound() {
            Bound::Included(&key) => int_from_key(key),
            Bound::Excluded(&key) => {
                let inclusive_end = K::Int::wrapping_decrement(int_from_key(key));
                if inclusive_end == K::Int::MAX {
                    // No key is below MIN, so the range is empty.
                    raw.node = NodeRef::INVALID;
                }
                inclusive_end
            }
            Bound::Unbounded => K::Int::MAX,
        };
        RangeMut {
            raw,
            inclusive_end,
            btree: self,
        }
    }
}

impl<K: BTreeKey, V, A: Allocator> IntoIterator for BTree<K, V, A> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            raw: self.raw_iter(),
            btree: ManuallyDrop::new(self),
        }
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> IntoIterator for &'a BTree<K, V, A> {
    type Item = (K, &'a V);

    type IntoIter = Iter<'a, K, V, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: BTreeKey, V, A: Allocator> IntoIterator for &'a mut BTree<K, V, A> {
    type Item = (K, &'a mut V);

    type IntoIter = IterMut<'a, K, V, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
