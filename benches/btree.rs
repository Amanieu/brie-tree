use std::{collections::BTreeMap, hint::black_box, ops::Bound};

use brie_tree::BTree;
use nonmax::NonMaxU32;

fn main() {
    divan::main();
}

fn lens() -> impl Iterator<Item = u32> {
    (0..20).map(|i| 1 << i)
}

trait KeyGen: Default {
    fn gen_key(&mut self, len: u32) -> NonMaxU32;
}

#[derive(Default)]
struct Seq(u32);
impl KeyGen for Seq {
    fn gen_key(&mut self, _len: u32) -> NonMaxU32 {
        let key = self.0;
        self.0 += 1;
        NonMaxU32::new(key).unwrap_or(NonMaxU32::new(0).unwrap())
    }
}

#[derive(Default)]
struct Rand(u32);
impl KeyGen for Rand {
    fn gen_key(&mut self, len: u32) -> NonMaxU32 {
        let key = self.0;
        self.0 = self.0.wrapping_mul(1664525).wrapping_add(1013904223);
        NonMaxU32::new(key % len).unwrap_or(NonMaxU32::new(0).unwrap())
    }
}

#[divan::bench(args = lens(), types = [Seq, Rand])]
fn lookup_btree<K: KeyGen>(bencher: divan::Bencher, len: u32) {
    let mut btree = BTree::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        let mut k = K::default();
        for _ in 0..len {
            let key = k.gen_key(len);
            black_box(btree.get(black_box(key)));
        }
    });
}

#[divan::bench(args = lens(), types = [Seq, Rand])]
fn lookup_std<K: KeyGen>(bencher: divan::Bencher, len: u32) {
    let mut btree = BTreeMap::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        let mut k = K::default();
        for _ in 0..len {
            let key = k.gen_key(len);
            black_box(btree.get(&black_box(key)));
        }
    });
}

#[divan::bench(args = lens(), types = [Seq, Rand])]
fn insert_btree<K: KeyGen>(bencher: divan::Bencher, len: u32) {
    bencher.bench_local(|| {
        let mut btree = BTree::new();
        let mut k = K::default();
        for _ in 0..len {
            let key = k.gen_key(len);
            btree.insert(key, key);
        }
        btree
    });
}

#[divan::bench(args = lens(), types = [Seq, Rand])]
fn insert_btree_reuse<K: KeyGen>(bencher: divan::Bencher, len: u32) {
    let mut btree = BTree::new();
    bencher.bench_local(|| {
        btree.clear();
        let mut k = K::default();
        for _ in 0..len {
            let key = k.gen_key(len);
            btree.insert(key, key);
        }
        divan::black_box(&btree);
    });
}

#[divan::bench(args = lens(), types = [Seq, Rand])]
fn insert_std<K: KeyGen>(bencher: divan::Bencher, len: u32) {
    bencher.bench_local(|| {
        let mut btree = BTreeMap::new();
        let mut k = K::default();
        for _ in 0..len {
            let key = k.gen_key(len);
            btree.insert(key, key);
        }
        btree
    });
}

#[divan::bench(args = lens())]
fn iter_btree(bencher: divan::Bencher, len: u32) {
    let mut btree = BTree::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        for (k, v) in &btree {
            divan::black_box((k, v));
        }
    });
}

#[divan::bench(args = lens())]
fn iter_std(bencher: divan::Bencher, len: u32) {
    let mut btree = BTreeMap::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        for (k, v) in &btree {
            divan::black_box((k, v));
        }
    });
}

#[divan::bench(args = lens())]
fn iter_std_rev(bencher: divan::Bencher, len: u32) {
    let mut btree = BTreeMap::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        for (k, v) in btree.iter().rev() {
            divan::black_box((k, v));
        }
    });
}

#[divan::bench(args = lens())]
fn iter_cursor(bencher: divan::Bencher, len: u32) {
    let mut btree = BTree::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        let mut cursor = btree.cursor();
        while let Some((k, v)) = cursor.entry() {
            divan::black_box((k, v));
            cursor.next();
        }
    });
}

#[divan::bench(args = lens())]
fn iter_cursor_rev(bencher: divan::Bencher, len: u32) {
    let mut btree = BTree::new();
    for i in 0..len {
        btree.insert(NonMaxU32::new(i).unwrap(), 0u32);
    }
    bencher.bench_local(|| {
        let mut cursor = btree.cursor_at(Bound::Unbounded);
        while cursor.prev() {
            divan::black_box(cursor.entry());
        }
    });
}
