use core::{assert_matches, ops::Bound};
use std::{
    panic::{AssertUnwindSafe, catch_unwind},
    sync::atomic::{AtomicUsize, Ordering},
};

use allocator_api2::alloc::Allocator;
use rand::{Rng, seq::SliceRandom};

use crate::{
    BTree, BTreeKey,
    int::BTreeInteger,
    node::{NodePos, NodeRef},
    stack::Height,
};

impl<K: BTreeKey, V, A: Allocator> BTree<K, V, A> {
    fn check_invariants(&self, assert_sorted: bool) {
        let mut last_leaf = None;
        self.check_node(
            self.root,
            self.height,
            assert_sorted,
            None,
            None,
            &mut last_leaf,
        );

        // Ensure the linked list of leaf nodes is properly terminated.
        assert_eq!(
            unsafe { last_leaf.unwrap().next_leaf(&self.leaf) },
            NodeRef::INVALID
        );
    }

    fn check_node(
        &self,
        node: NodeRef,
        height: Height<K::Int>,
        assert_sorted: bool,
        min: Option<<K::Int as BTreeInteger>::Raw>,
        max: Option<<K::Int as BTreeInteger>::Raw>,
        prev_leaf: &mut Option<NodeRef>,
    ) {
        let Some(down) = height.down() else {
            self.check_leaf_node(node, assert_sorted, min, max, prev_leaf);
            return;
        };

        let keys = || {
            (0..K::Int::B).map(|i| unsafe { node.key(NodePos::new_unchecked(i), &self.internal) })
        };

        // The last 2 keys must be MAX.
        assert_eq!(keys().nth(K::Int::B - 1).unwrap(), K::Int::MAX);
        assert_eq!(keys().nth(K::Int::B - 2).unwrap(), K::Int::MAX);

        let end = unsafe { node.end_internal(&self.internal) };
        assert!(end > pos!(0));
        assert!(keys().skip(end.index() - 1).all(|key| key == K::Int::MAX));

        // Keys must be sorted in increasing order.
        if assert_sorted {
            assert!(keys().is_sorted_by(|&a, &b| K::Int::cmp(a, b).is_le()));
            if let Some(min) = min {
                assert!(keys().all(|key| K::Int::cmp(key, min).is_ge()));
            }
            if let Some(max) = max {
                assert!(
                    keys()
                        .take(end.index() - 1)
                        .all(|key| K::Int::cmp(key, max).is_le())
                );
            }
        }

        let is_root = height == self.height;

        // Non-root nodes must be at least half full. Non-leaf root nodes must
        // have at least 2 elements.
        if is_root {
            assert!(end >= pos!(2));
        } else {
            assert!(end >= pos!(K::Int::B / 2));
        }

        // Check the invariants for child nodes.
        let mut prev_key = min;
        for i in 0..end.index() {
            unsafe {
                let pos = NodePos::new_unchecked(i);
                let key = node.key(pos, &self.internal);
                let value = node.value(pos, &self.internal).assume_init_read();
                self.check_node(
                    value,
                    down,
                    assert_sorted,
                    prev_key,
                    if i + 1 == end.index() { max } else { Some(key) },
                    prev_leaf,
                );
                prev_key = Some(key);
            }
        }
    }

    fn check_leaf_node(
        &self,
        node: NodeRef,
        assert_sorted: bool,
        min: Option<<K::Int as BTreeInteger>::Raw>,
        max: Option<<K::Int as BTreeInteger>::Raw>,
        prev_leaf: &mut Option<NodeRef>,
    ) {
        let keys =
            || (0..K::Int::B).map(|i| unsafe { node.key(NodePos::new_unchecked(i), &self.leaf) });

        // All keys at or past end must be MAX.
        assert_eq!(keys().nth(K::Int::B - 1).unwrap(), K::Int::MAX);

        let end = unsafe { node.end(&self.leaf) };
        assert!(keys().skip(end.index()).all(|key| key == K::Int::MAX));

        // Keys must be sorted in increasing order.
        if assert_sorted {
            assert!(keys().is_sorted_by(|&a, &b| K::Int::cmp(a, b).is_le()));
            if let Some(min) = min {
                assert!(keys().all(|key| K::Int::cmp(key, min).is_ge()));
            }
            if let Some(max) = max {
                assert!(
                    keys()
                        .take(end.index())
                        .all(|key| K::Int::cmp(key, max).is_le())
                );
            }
        }

        let is_root = self.height == Height::leaf();

        // Non-root nodes must be at least half full.
        if !is_root {
            assert!(end >= pos!(K::Int::B / 2));
        }

        // An explicit sub-tree maximum, including MAX, must match the last key.
        // Only the right-most path has no explicit maximum.
        if let Some(max) = max {
            assert_eq!(keys().nth(end.index() - 1).unwrap(), max);
        }

        // The first leaf node must always have an offset of 0.
        if prev_leaf.is_none() {
            assert_eq!(node, NodeRef::zero());
        }

        // Ensure the linked list of leaf nodes is correct.
        if let Some(prev_leaf) = prev_leaf {
            assert_eq!(unsafe { prev_leaf.next_leaf(&self.leaf) }, node);
        }

        *prev_leaf = Some(node);
    }
}

#[test]
fn integer_extrema() {
    macro_rules! check {
        ($($int:ty),*) => {$( {
            let mut tree = BTree::<$int, u32>::new();
            tree.get(<$int>::MAX);
            for key in [<$int>::MAX, <$int>::MIN, <$int>::MAX - 1, 0] {
                tree.insert(key, 0);
                tree.check_invariants(true);
            }
            tree.range(..<$int>::MAX).count();
            tree.range(<$int>::MAX..=<$int>::MAX).count();
            tree.range(..=<$int>::MAX).count();
            tree.range(..<$int>::MIN).count();
            tree.range(..=<$int>::MIN).count();
            tree.range(..(<$int>::MIN + 1)).count();
            tree.range(..).count();
            tree.range_mut(..<$int>::MIN).count();
            tree.range_mut(..=<$int>::MIN).count();
            tree.range_mut(..(<$int>::MIN + 1)).count();
            tree.range_mut(..<$int>::MAX).count();
            tree.range_mut(..).count();
            tree.iter_from(Bound::Excluded(<$int>::MAX)).count();
            tree.range((Bound::Excluded(<$int>::MAX), Bound::Unbounded)).count();
            tree.cursor_at(Bound::Excluded(<$int>::MAX)).entry();
            tree.cursor_at(Bound::Included(<$int>::MAX)).entry();
            let mut cursor = tree.cursor_at(Bound::Unbounded);
            cursor.prev();
            cursor.entry();
            cursor.next();
            cursor.iter().next();
            let mut cursor = tree.cursor_mut_at(Bound::Unbounded);
            cursor.iter().next();
            cursor.iter_mut().next();
            cursor.into_iter().next();
            tree.cursor_mut_at(Bound::Unbounded).into_iter_mut().next();
            *tree.get_mut(<$int>::MAX).unwrap() = 1;
            for (_, value) in tree.range_mut(<$int>::MAX..=<$int>::MAX) {
                *value += 1;
            }
            tree.iter_mut_from(Bound::Excluded(<$int>::MAX)).count();
            tree.remove(<$int>::MAX);
            tree.check_invariants(true);
            tree.get(<$int>::MAX);
            // Repeated calls after exhaustion must remain safe and return None.
            let mut iter = tree.iter();
            while iter.next().is_some() {}
            iter.next();
            let mut range = tree.range(..0);
            while range.next().is_some() {}
            range.next();
            let mut range = tree.range_mut(..0);
            while range.next().is_some() {}
            range.next();
            tree.clear();
            tree.check_invariants(true);
            tree.iter().next();
            tree.cursor_at(Bound::Unbounded).iter().next();
            tree.into_iter().next();
        } )*};
    }
    check!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
}

#[test]
fn max_duplicates_rebalance() {
    // Small fanout forces MAX separators through several internal levels.
    let mut tree = BTree::<u128, usize>::new();
    for value in 0..128 {
        tree.cursor_mut_at(Bound::Unbounded)
            .insert_before(u128::MAX, value);
        tree.check_invariants(true);
    }
    tree.range(u128::MAX..=u128::MAX).count();
    let mut cursor = tree.cursor_at(Bound::Unbounded);
    while cursor.prev() {
        cursor.entry();
    }
    while !cursor.is_end() {
        cursor.entry();
        cursor.next();
    }

    // Remove alternately from both ends to exercise both sibling choices,
    // steals, merges, and eventual collapse back to an empty leaf root.
    for i in 0..128 {
        if i % 2 == 0 {
            tree.cursor_mut().remove();
        } else {
            let mut cursor = tree.cursor_mut_at(Bound::Unbounded);
            cursor.prev();
            cursor.replace(u128::MAX, usize::MAX);
            cursor.remove();
        }
        tree.check_invariants(true);
    }
    tree.insert(u128::MAX, 42);
    tree.check_invariants(true);
}

#[test]
fn unordered_max_cursor_edits() {
    // Cursor edits promise memory safety even when keys are out of order.
    // In particular, a live MAX must not hide later live entries.
    let mut tree = BTree::<u128, u32>::new();
    for value in 0..100 {
        let key = if value % 2 == 0 { u128::MAX } else { 0 };
        let mut cursor = tree.cursor_mut_at(Bound::Unbounded);
        if cursor.prev() {
            cursor.insert_after(key, value);
        } else {
            cursor.insert_before(key, value);
        }
        tree.check_invariants(false);
    }
    tree.values().count();
    for key in [0, 1, u128::MAX - 1, u128::MAX] {
        // Results may be incorrect, but searching must remain safe.
        tree.get(key);
    }
    for value in 0..100 {
        let mut cursor = tree.cursor_mut();
        cursor.replace(u128::MAX, value);
        cursor.remove();
        tree.check_invariants(false);
    }
}

#[test]
fn max_metadata_layouts_and_drop() {
    #[repr(align(256))]
    struct Aligned {
        _value: Box<u8>,
    }
    let mut tree = BTree::<u128, Aligned>::new();
    for _ in 0..100 {
        tree.insert(
            u128::MAX,
            Aligned {
                _value: Box::new(0),
            },
        );
        tree.check_invariants(true);
    }
    let mut iter = tree.into_iter();
    drop(iter.next());
    drop(iter);

    // A zero-sized value puts metadata immediately after the keys; byte-sized
    // values require padding to align the metadata word.
    let mut zst = BTree::<u8, ()>::new();
    let mut bytes = BTree::<u8, u8>::new();
    for _ in 0..256 {
        zst.insert(u8::MAX, ());
        zst.check_invariants(true);
        bytes.insert(u8::MAX, 1);
        bytes.check_invariants(true);
    }
    zst.iter().count();
    bytes.iter().count();
    for _ in 0..256 {
        zst.remove(u8::MAX);
        zst.check_invariants(true);
        bytes.remove(u8::MAX);
        bytes.check_invariants(true);
    }
}

fn assert_keys_values(btree: &BTree<u32, u32>, expected: &[u32]) {
    let keys: Vec<_> = btree.keys().collect();
    let values: Vec<_> = btree.values().copied().collect();
    assert_eq!(expected, keys);
    assert_eq!(expected, values);
}

#[test]
fn insert_sorted() {
    let mut btree = BTree::new();
    btree.check_invariants(true);
    let input: Vec<_> = (0..1000u32).collect();
    for &i in &input {
        btree.insert(i, i);
        btree.check_invariants(true);
    }
    let keys: Vec<_> = btree.keys().collect();
    let values: Vec<_> = btree.values().copied().collect();
    assert_eq!(input, keys);
    assert_eq!(input, values);
}

#[test]
fn insert_random() {
    let mut btree = BTree::new();
    btree.check_invariants(true);
    let input: Vec<_> = (0..1000u32).collect();
    let mut shuffled = input.clone();
    shuffled.shuffle(&mut rand::rng());
    for &i in &shuffled {
        btree.insert(i, i);
        btree.check_invariants(true);
    }
    let keys: Vec<_> = btree.keys().collect();
    let values: Vec<_> = btree.values().copied().collect();
    assert_eq!(input, keys);
    assert_eq!(input, values);
}

#[test]
fn insert_before_preserves_cursor_position() {
    let mut btree = BTree::new();
    for i in [0, 10, 20] {
        btree.insert(i, i);
    }

    let mut cursor = btree.cursor_mut_at(Bound::Included(10));
    cursor.insert_before(5, 5);
    assert_matches!(cursor.entry(), Some((10, _)));
    drop(cursor);

    let mut cursor = btree.cursor_mut_at(Bound::Unbounded);
    cursor.insert_before(30, 30);
    assert_matches!(cursor.entry(), None);
    drop(cursor);

    btree.check_invariants(true);
    assert_keys_values(&btree, &[0, 5, 10, 20, 30]);
}

#[test]
fn insert_before_preserves_cursor_position_after_split() {
    let mut btree = BTree::new();
    let node_len = <u32 as BTreeInteger>::B - 1;
    for i in 0..node_len as u32 {
        btree.insert(i * 2, i * 2);
    }

    let successor_index = node_len as u32 / 2;
    let successor = successor_index * 2;
    let mut cursor = btree.cursor_mut_at(Bound::Included(successor));
    cursor.insert_before(successor_index * 2 - 1, successor_index * 2 - 1);
    assert_eq!(cursor.entry().map(|(k, _v)| k), Some(successor));
    drop(cursor);

    let mut cursor = btree.cursor_mut_at(Bound::Unbounded);
    cursor.insert_before(node_len as u32 * 2, node_len as u32 * 2);
    assert_matches!(cursor.entry(), None);
    drop(cursor);

    btree.check_invariants(true);
    let mut expected: Vec<_> = (0..node_len as u32).map(|i| i * 2).collect();
    expected.insert(successor_index as usize, successor_index * 2 - 1);
    expected.push(node_len as u32 * 2);
    assert_keys_values(&btree, &expected);
}

#[test]
fn remove() {
    let mut btree = BTree::new();
    let mut input: Vec<_> = (0..1000u32).collect();
    let mut shuffled = input.clone();
    shuffled.shuffle(&mut rand::rng());
    for &i in &input {
        if i % 2 != 0 {
            continue;
        }
        btree.insert(i, i);
    }
    btree.check_invariants(true);

    while !input.is_empty() {
        let idx = rand::rng().random_range(..input.len());
        let key = input.remove(idx);
        let entry = btree.remove(key);
        if key % 2 == 0 {
            let value = entry.unwrap();
            assert_eq!(value, key);
        } else {
            assert_matches!(entry, None);
        }
        btree.check_invariants(true);

        let keys: Vec<_> = btree.keys().collect();
        let values: Vec<_> = btree.values().copied().collect();
        let filtered_input: Vec<_> = input.iter().filter(|&&i| i % 2 == 0).copied().collect();
        assert_eq!(filtered_input, keys);
        assert_eq!(filtered_input, values);
    }
}

#[test]
fn iter() {
    let mut btree = BTree::new();
    let input: Vec<_> = (0..1000u32).collect();
    let mut shuffled = input.clone();
    shuffled.shuffle(&mut rand::rng());
    for &i in &shuffled {
        btree.insert(i, i);
    }

    let keys: Vec<_> = btree.keys().collect();
    let values: Vec<_> = btree.values().copied().collect();
    assert_eq!(input, keys);
    assert_eq!(input, values);
}

#[allow(dead_code)]
fn require_send<T: Send>() {}
#[allow(dead_code)]
fn require_sync<T: Sync>() {}
#[allow(dead_code)]
fn require_unpin<T: Unpin>() {}
#[allow(dead_code)]
fn check_send<K: Send + BTreeKey, V: Send>() {
    require_send::<BTree<K, V>>();
}
#[allow(dead_code)]
fn check_sync<K: Sync + BTreeKey, V: Sync>() {
    require_sync::<BTree<K, V>>();
}
#[allow(dead_code)]
fn check_unpin<K: Unpin + BTreeKey, V: Unpin>() {
    require_unpin::<BTree<K, V>>();
}

#[test]
fn clear_with_panicking_value() {
    static DROPS: [AtomicUsize; 4] = [
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
    ];

    struct DropValue {
        index: usize,
        panic: bool,
    }

    impl Drop for DropValue {
        fn drop(&mut self) {
            DROPS[self.index].fetch_add(1, Ordering::Relaxed);
            assert!(!self.panic, "value destructor panicked");
        }
    }

    for drops in &DROPS {
        drops.store(0, Ordering::Relaxed);
    }
    let mut btree = BTree::new();
    for (index, panic) in [(0, false), (1, true), (2, false)] {
        btree.insert(index as u32, DropValue { index, panic });
    }

    let result = catch_unwind(AssertUnwindSafe(|| btree.clear()));
    assert_matches!(result, Err(_));
    assert!(btree.is_empty());
    btree.check_invariants(true);
    assert_eq!(
        DROPS.each_ref().map(|drops| drops.load(Ordering::Relaxed)),
        [1, 1, 0, 0]
    );

    // The restored root can be re-used without exposing or dropping any of the
    // values which were discarded when clear unwound.
    btree.insert(
        3,
        DropValue {
            index: 3,
            panic: false,
        },
    );
    drop(btree);
    assert_eq!(
        DROPS.each_ref().map(|drops| drops.load(Ordering::Relaxed)),
        [1, 1, 0, 1]
    );
}
