#![no_main]

use std::{fmt::Debug, ops::Bound};

use arbitrary::{Arbitrary, Result, Unstructured};
use brie_tree::{BTree, BTreeKey, nonmax::*};
use libfuzzer_sys::fuzz_target;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Key<Int>(Int);

macro_rules! impl_key {
    ($($int:ident $nonmax:ident,)*) => {
        $(
            impl<'a> Arbitrary<'a> for Key<$nonmax> {
                fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                    Ok(Key(
                        $nonmax::new(u.int_in_range(0..=$int::MAX - 1)?).unwrap()
                    ))
                }
            }
            impl BTreeKey for Key<$nonmax> {
                type Int = $nonmax;

                fn to_int(self) -> Self::Int {
                    self.0
                }

                fn from_int(int: Self::Int) -> Self {
                    Self(int)
                }
            }
        )*
    };
}

impl_key! {
    u8 NonMaxU8,
    u16 NonMaxU16,
    u32 NonMaxU32,
    u64 NonMaxU64,
    u128 NonMaxU128,
    i8 NonMaxI8,
    i16 NonMaxI16,
    i32 NonMaxI32,
    i64 NonMaxI64,
    i128 NonMaxI128,
}

#[derive(Arbitrary, Debug)]
enum Action<Key, Value> {
    Clear,
    Insert(Key, Value),
    InsertMulti(Key, Value),
    Get(Key),
    Remove(Key),
    Range(Bound<Key>, Bound<Key>),
    Cursor(Option<Bound<Key>>, Vec<CursorAction>),
    CursorMut(Option<Bound<Key>>, Vec<CursorMutAction<Key, Value>>),
}

#[derive(Arbitrary, Debug)]
enum CursorAction {
    Next,
    Prev,
}

#[derive(Arbitrary, Debug)]
enum CursorMutAction<Key, Value> {
    Next,
    Prev,
    InsertBefore(Key, Value),
    InsertAfter(Value),
    Replace(Value),
    Remove,
}

#[derive(Arbitrary, Debug)]
enum KeyType<Value> {
    U8(Vec<Action<Key<NonMaxU8>, Value>>),
    U16(Vec<Action<Key<NonMaxU16>, Value>>),
    U32(Vec<Action<Key<NonMaxU32>, Value>>),
    U64(Vec<Action<Key<NonMaxU64>, Value>>),
    U128(Vec<Action<Key<NonMaxU128>, Value>>),
    I8(Vec<Action<Key<NonMaxI8>, Value>>),
    I16(Vec<Action<Key<NonMaxI16>, Value>>),
    I32(Vec<Action<Key<NonMaxI32>, Value>>),
    I64(Vec<Action<Key<NonMaxI64>, Value>>),
    I128(Vec<Action<Key<NonMaxI128>, Value>>),
}

#[derive(Arbitrary, Debug)]
enum ValueType {
    Empty(KeyType<()>),
    U8(KeyType<u8>),
    U16(KeyType<u16>),
    U32(KeyType<u32>),
    U64(KeyType<u64>),
    U128(KeyType<u128>),
}

fn run<
    'a,
    Key: Ord + BTreeKey + Arbitrary<'a> + Debug,
    Value: Eq + Arbitrary<'a> + Debug + Copy,
>(
    actions: Vec<Action<Key, Value>>,
) {
    {
        let mut btree = BTree::new();
        let mut vec = vec![];
        for action in actions {
            match action {
                Action::Clear => {
                    btree.clear();
                    vec.clear();
                }
                Action::Insert(key, value) => {
                    let old = btree.insert(key, value);
                    let index = vec.partition_point(|&(k, _v)| k < key);
                    if index != vec.len() && vec[index].0 == key {
                        assert_eq!(old, Some(vec[index].1));
                        vec[index].1 = value;
                    } else {
                        vec.insert(index, (key, value));
                        assert_eq!(old, None);
                    }
                }
                Action::InsertMulti(key, value) => {
                    btree.insert_multi(key, value);
                    let index = vec.partition_point(|&(k, _v)| k < key);
                    vec.insert(index, (key, value));
                }
                Action::Get(key) => {
                    let value = btree.get(key);
                    let index = vec.partition_point(|&(k, _v)| k < key);
                    if index != vec.len() && vec[index].0 == key {
                        assert_eq!(value, Some(&vec[index].1));
                    } else {
                        assert_eq!(value, None);
                    }
                }
                Action::Remove(key) => {
                    let value = btree.remove(key);
                    let index = vec.partition_point(|&(k, _v)| k < key);
                    if index != vec.len() && vec[index].0 == key {
                        assert_eq!(value, Some(vec[index].1));
                        vec.remove(index);
                    } else {
                        assert_eq!(value, None);
                    }
                }
                Action::Range(start, end) => {
                    let range = btree.range((start, end));
                    let entries: Vec<_> = range.map(|(k, &v)| (k, v)).collect();
                    let start = match start {
                        Bound::Unbounded => 0,
                        Bound::Included(key) => vec.partition_point(|&(k, _v)| k < key),
                        Bound::Excluded(key) => vec.partition_point(|&(k, _v)| k <= key),
                    };
                    let end = match end {
                        Bound::Unbounded => vec.len(),
                        Bound::Included(key) => vec.partition_point(|&(k, _v)| k <= key),
                        Bound::Excluded(key) => vec.partition_point(|&(k, _v)| k < key),
                    };
                    assert_eq!(vec[start.min(end)..end], entries);
                }
                Action::Cursor(key, actions) => {
                    let (mut cursor, mut index) = if let Some(key) = key {
                        (
                            btree.cursor_at(key),
                            match key {
                                Bound::Unbounded => vec.len(),
                                Bound::Included(key) => vec.partition_point(|&(k, _v)| k < key),
                                Bound::Excluded(key) => vec.partition_point(|&(k, _v)| k <= key),
                            },
                        )
                    } else {
                        (btree.cursor(), 0)
                    };
                    let entries: Vec<_> = cursor.iter().map(|(k, &v)| (k, v)).collect();
                    assert_eq!(entries, vec[index..]);

                    for action in actions {
                        match action {
                            CursorAction::Next => {
                                if index != vec.len() {
                                    cursor.next();
                                    index += 1;
                                }
                            }
                            CursorAction::Prev => {
                                let ok = cursor.prev();
                                assert_eq!(ok, index != 0);
                                if ok {
                                    index -= 1;
                                }
                            }
                        }
                        assert_eq!(cursor.is_end(), index == vec.len());
                        let entries: Vec<_> = cursor.iter().map(|(k, &v)| (k, v)).collect();
                        assert_eq!(entries, vec[index..]);
                    }
                }
                Action::CursorMut(key, actions) => {
                    let (mut cursor, mut index) = if let Some(key) = key {
                        (
                            btree.cursor_mut_at(key),
                            match key {
                                Bound::Unbounded => vec.len(),
                                Bound::Included(key) => vec.partition_point(|&(k, _v)| k < key),
                                Bound::Excluded(key) => vec.partition_point(|&(k, _v)| k <= key),
                            },
                        )
                    } else {
                        (btree.cursor_mut(), 0)
                    };
                    let entries: Vec<_> = cursor.iter().map(|(k, &v)| (k, v)).collect();
                    assert_eq!(entries, vec[index..]);

                    for action in actions {
                        match action {
                            CursorMutAction::Next => {
                                if index != vec.len() {
                                    cursor.next();
                                    index += 1;
                                }
                            }
                            CursorMutAction::Prev => {
                                let ok = cursor.prev();
                                assert_eq!(ok, index != 0);
                                if ok {
                                    index -= 1;
                                }
                            }
                            CursorMutAction::InsertBefore(key, value) => {
                                let key = if vec.is_empty() {
                                    key
                                } else if index == vec.len() {
                                    vec[index - 1].0
                                } else {
                                    vec[index].0
                                };
                                cursor.insert_before(key, value);
                                vec.insert(index, (key, value));
                            }
                            CursorMutAction::InsertAfter(value) => {
                                if index != vec.len() {
                                    let key = vec[index].0;
                                    cursor.insert_after(key, value);
                                    vec.insert(index + 1, (key, value));
                                }
                            }
                            CursorMutAction::Replace(value) => {
                                if index != vec.len() {
                                    let entry = cursor.replace(vec[index].0, value);
                                    let vec_entry = vec[index];
                                    assert_eq!(entry, vec_entry);
                                    vec[index].1 = value;
                                }
                            }
                            CursorMutAction::Remove => {
                                if index != vec.len() {
                                    let entry = cursor.remove();
                                    let vec_entry = vec.remove(index);
                                    assert_eq!(entry, vec_entry);
                                }
                            }
                        }
                        let entries: Vec<_> = cursor.iter().map(|(k, &v)| (k, v)).collect();
                        assert_eq!(entries, vec[index..]);
                        assert_eq!(
                            cursor.entry().map(|(k, &v)| (k, v)),
                            vec.get(index).copied()
                        );
                        assert_eq!(cursor.is_end(), index == vec.len());
                    }
                }
            }

            assert_eq!(vec.is_empty(), btree.is_empty());
            let btree_entries: Vec<_> = btree.iter().map(|(k, &v)| (k, v)).collect();
            assert_eq!(vec, btree_entries);
        }
    }
}

fn dispatch_by_key<'a, Value: Eq + Arbitrary<'a> + Debug + Copy>(actions: KeyType<Value>) {
    match actions {
        KeyType::U8(actions) => run(actions),
        KeyType::U16(actions) => run(actions),
        KeyType::U32(actions) => run(actions),
        KeyType::U64(actions) => run(actions),
        KeyType::U128(actions) => run(actions),
        KeyType::I8(actions) => run(actions),
        KeyType::I16(actions) => run(actions),
        KeyType::I32(actions) => run(actions),
        KeyType::I64(actions) => run(actions),
        KeyType::I128(actions) => run(actions),
    }
}

fuzz_target!(|actions: ValueType| {
    match actions {
        ValueType::Empty(actions) => dispatch_by_key(actions),
        ValueType::U8(actions) => dispatch_by_key(actions),
        ValueType::U16(actions) => dispatch_by_key(actions),
        ValueType::U32(actions) => dispatch_by_key(actions),
        ValueType::U64(actions) => dispatch_by_key(actions),
        ValueType::U128(actions) => dispatch_by_key(actions),
    }
});
