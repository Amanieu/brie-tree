# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0](https://github.com/Amanieu/brie-tree/compare/brie-tree-v0.1.2...brie-tree-v0.2.0) - 2026-10-27

### Added

- Add `BTree::from_sorted_iter`, `BTree::from_sorted_iter_in`, and
  `BTree::append_sorted` for efficient bulk loading of sorted entries. Duplicate
  keys and their input order are preserved. When appending, new keys must be at
  least the greatest key already in the tree.

### Changed

- **Breaking:** Keys now use fixed-width primitive integers (`u8` through `u128`
  and `i8` through `i128`) instead of `NonMax` types, supporting the full
  integer range, including the maximum value. The `nonmax` re-export is removed.
  Custom `BTreeKey` implementations must use a primitive integer for
  `BTreeKey::Int`.
- **Breaking:** `BTree` now always acts as a multi-map. `insert` preserves
  existing entries with the same key and returns `()` instead of `Option<V>`.
  `insert_multi` is removed; use `insert` instead. `Extend` and `FromIterator`
  also preserve all duplicate entries. `get`, `get_mut`, and `remove` continue
  to operate on one arbitrarily chosen entry with the given key.
- **Breaking:** `CursorMut::insert_before` now keeps the cursor on the original
  entry instead of the inserted entry. A cursor at the end remains at the end.
- Raise the minimum supported Rust version from 1.88 to 1.98.
- Make tree cloning more efficient and preserve duplicate entries and their
  order.

### Fixed

- Leave the tree empty and usable if a value destructor panics during
  `BTree::clear`.
- Fix memory leaks when dropping a tree or owning iterator if a value destructor
  panics, and ensure the owning iterator's allocator is dropped.
- Fix invalid deallocation when dropping trees with no internal nodes.
- Fix out-of-bounds accesses when using cursors on trees at the maximum height.
- Fix lookups on big-endian AArch64 targets.
- Fix builds for 32-bit RISC-V targets with vector support.

## [0.1.2](https://github.com/Amanieu/brie-tree/compare/brie-tree-v0.1.1...brie-tree-v0.1.2) - 2025-07-13

### Other

- Test MSRV now that 1.88 is stable
- Fix clippy lints
- Avoid `PhantomData` that inhibit `Send` and `Sync`

## [0.1.1](https://github.com/Amanieu/brie-tree/compare/brie-tree-v0.1.0...brie-tree-v0.1.1) - 2025-07-12

### Other

- Implement `Send` and `Sync` for `NodePool`

## [0.1.0](https://github.com/Amanieu/brie-tree/releases/tag/brie-tree-v0.1.0) - 2025-06-13

### Other

- Initial commit
