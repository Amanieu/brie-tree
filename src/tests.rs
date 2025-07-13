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
            K::Int::MAX,
            &mut last_leaf,
        );

        // Ensure the linked list of leaf nodes is properly terminated.
        assert_eq!(unsafe { last_leaf.unwrap().next_leaf(&self.leaf) }, None);
    }

    fn check_node(
        &self,
        node: NodeRef,
        height: Height<K::Int>,
        assert_sorted: bool,
        min: Option<<K::Int as BTreeInteger>::Raw>,
        max: <K::Int as BTreeInteger>::Raw,
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

        // All MAX keys must be after non-MAX keys,
        assert!(keys().is_sorted_by_key(|key| key == K::Int::MAX));

        // Keys must be sorted in increasing order.
        if assert_sorted {
            assert!(keys().is_sorted_by(|&a, &b| K::Int::cmp(a, b).is_le()));
            if let Some(min) = min {
                assert!(keys().all(|key| K::Int::cmp(key, min).is_ge()));
            }
            assert!(keys().all(|key| key == K::Int::MAX || K::Int::cmp(key, max).is_le()));
        }

        let len = keys().take_while(|&key| key != K::Int::MAX).count() + 1;
        let is_root = height == self.height;

        // Non-root nodes must be at least half full. Non-leaf root nodes must
        // have at least 2 elements.
        if is_root {
            assert!(len >= 2);
        } else {
            assert!(len >= K::Int::B / 2);
        }

        // Check the invariants for child nodes.
        let mut prev_key = min;
        for i in 0..len {
            unsafe {
                let pos = NodePos::new_unchecked(i);
                let key = node.key(pos, &self.internal);
                let value = node.value(pos, &self.internal).assume_init_read();
                self.check_node(
                    value,
                    down,
                    assert_sorted,
                    prev_key,
                    if key == K::Int::MAX { max } else { key },
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
        max: <K::Int as BTreeInteger>::Raw,
        prev_leaf: &mut Option<NodeRef>,
    ) {
        let keys =
            || (0..K::Int::B).map(|i| unsafe { node.key(NodePos::new_unchecked(i), &self.leaf) });

        // The last key must be MAX.
        assert_eq!(keys().nth(K::Int::B - 1).unwrap(), K::Int::MAX);

        // All MAX keys must be after non-MAX keys,
        assert!(keys().is_sorted_by_key(|key| key == K::Int::MAX));

        // Keys must be sorted in increasing order.
        if assert_sorted {
            assert!(keys().is_sorted_by(|&a, &b| K::Int::cmp(a, b).is_le()));
            if let Some(min) = min {
                assert!(keys().all(|key| K::Int::cmp(key, min).is_ge()));
            }
            assert!(keys().all(|key| key == K::Int::MAX || K::Int::cmp(key, max).is_le()));
        }

        let len = keys().take_while(|&key| key != K::Int::MAX).count();
        let is_root = self.height == Height::leaf();

        // Non-root nodes must be at least half full.
        if !is_root {
            assert!(len >= K::Int::B / 2);
        }

        // The last key must be equal to the maximum for this sub-tree.
        if max != K::Int::MAX {
            assert_eq!(keys().nth(len - 1).unwrap(), max);
        }

        // The first leaf node must always have an offset of 0.
        if prev_leaf.is_none() {
            assert_eq!(node, NodeRef::zero());
        }

        // Ensure the linked list of leaf nodes is correct.
        if let Some(prev_leaf) = prev_leaf {
            assert_eq!(unsafe { prev_leaf.next_leaf(&self.leaf) }, Some(node));
        }

        *prev_leaf = Some(node);
    }
}

type Key = nonmax::NonMaxU32;

#[test]
fn insert_sorted() {
    let mut btree = BTree::new();
    btree.check_invariants(true);
    let input: Vec<_> = (0..1000).map(|i| Key::new(i).unwrap()).collect();
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
    let input: Vec<_> = (0..1000).map(|i| Key::new(i).unwrap()).collect();
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
fn remove() {
    let mut btree = BTree::new();
    let mut input: Vec<_> = (0..1000).map(|i| Key::new(i).unwrap()).collect();
    let mut shuffled = input.clone();
    shuffled.shuffle(&mut rand::rng());
    for &i in &input {
        if i.get() % 2 != 0 {
            continue;
        }
        btree.insert(i, i);
    }
    btree.check_invariants(true);

    while !input.is_empty() {
        let idx = rand::rng().random_range(..input.len());
        let key = input.remove(idx);
        let entry = btree.remove(key);
        if key.get() % 2 == 0 {
            let value = entry.unwrap();
            assert_eq!(value, key);
        } else {
            assert!(entry.is_none());
        }
        btree.check_invariants(true);

        let keys: Vec<_> = btree.keys().collect();
        let values: Vec<_> = btree.values().copied().collect();
        let filtered_input: Vec<_> = input.iter().filter(|i| i.get() % 2 == 0).copied().collect();
        assert_eq!(filtered_input, keys);
        assert_eq!(filtered_input, values);
    }
}

#[test]
fn iter() {
    let mut btree = BTree::new();
    let input: Vec<_> = (0..1000).map(|i| Key::new(i).unwrap()).collect();
    let mut shuffled = input.clone();
    shuffled.shuffle(&mut rand::rng());
    for &i in &input {
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
