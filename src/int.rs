use core::{cmp::Ordering, fmt::Debug, mem, ops::IndexMut};

use crate::{
    BTreeKey,
    node::{NodePos, NodeRef},
    simd::SimdSearch,
    stack::{Height, Stack, max_height},
};

/// Helper function to convert a key directly to a raw integer.
#[inline]
pub(crate) fn int_from_key<K: BTreeKey>(key: K) -> <K::Int as BTreeInteger>::Raw {
    key.to_int().to_raw()
}

/// Helper function to convert a raw integer to a key.
#[inline]
pub(crate) fn key_from_int<K: BTreeKey>(int: <K::Int as BTreeInteger>::Raw) -> Option<K> {
    K::Int::from_raw(int).map(K::from_int)
}

/// B is selected so that all the keys fit in 128 bytes (2 cache lines).
pub(crate) const KEYS_BYTES: usize = 128;

/// Nodes are aligned to 128 bytes so they fit exactly in cache lines.
#[repr(C, align(128))]
pub(crate) struct AlignedKeys<T>(pub(crate) T);

/// This trait covers all operations that are specific to the integer type used
/// as a key.
///
/// # Safety
///
/// All items must be implemented as documented.
pub(crate) unsafe trait BTreeInteger: Copy + Eq + Debug {
    /// Number of elements per node, which must be at least 4.
    ///
    /// The number of elements may vary depending on the integer size to fit in
    /// cache lines or to make optimal use of SIMD instructions.
    const B: usize;

    /// Maximum integer value.
    ///
    /// `search` and `cmp` must compare this as larger than any other integer
    /// value.
    const MAX: Self::Raw;

    /// Raw integer type that is actually stored in the tree.
    type Raw: Copy + Eq + Debug + SimdSearch;

    /// Conversion from a `Self` to a raw integer.
    fn to_raw(self) -> Self::Raw;

    /// Conversion from a raw integer to a `Self`.
    fn from_raw(int: Self::Raw) -> Option<Self>;

    /// Compares 2 integers. We don't just use the `Ord` trait here because some
    /// implementations add a bias to the integer values.
    fn cmp(a: Self::Raw, b: Self::Raw) -> Ordering;

    /// Increments a raw integer by 1.
    fn increment(int: Self::Raw) -> Self::Raw;

    /// Array of keys used for SIMD comparison in `rank`.
    ///
    /// This must have the same layout as `[Self; Self::B]`.
    type Keys;

    /// Returns the index of the first key greater than or equal to `search`.
    ///
    /// Because this assumes that keys are sorted, it can be implemented either
    /// as a binary search or by counting the number of keys less than `search`.
    ///
    ///  # Safety
    ///
    /// The last key must be `Self::MAX`, which guarantees that the returned
    /// position is less than `Self::B`.
    unsafe fn search(keys: &Self::Keys, search: Self::Raw) -> NodePos<Self>;

    /// Array of `(NodeRef, NodePos)` pairs which can be indexed by a `Height`.
    type Stack: IndexMut<Height<Self>, Output = (NodeRef, NodePos<Self>)> + Default + Clone;
}

macro_rules! impl_int {
    ($($int:ident $nonmax:ident,)*) => {
        $(
            unsafe impl BTreeInteger for nonmax::$nonmax {
                const B: usize = KEYS_BYTES / mem::size_of::<Self>();

                const MAX: Self::Raw = $int::MAX.wrapping_add(Self::Raw::BIAS);

                type Raw = $int;

                #[inline]
                fn to_raw(self) -> Self::Raw {
                    self.get().wrapping_add(Self::Raw::BIAS)
                }

                #[inline]
                fn from_raw(int: Self::Raw) -> Option<Self> {
                    Self::new(int.wrapping_sub(Self::Raw::BIAS))
                }

                #[inline]
                fn cmp(a: Self::Raw, b: Self::Raw) -> Ordering {
                    Self::Raw::bias_cmp(a, b)
                }

                #[inline]
                fn increment(int: Self::Raw) -> Self::Raw {
                    int.wrapping_add(1)
                }

                type Keys = AlignedKeys<[Self::Raw; Self::B]>;

                #[inline]
                unsafe fn search(keys: &Self::Keys, search: Self::Raw) -> NodePos<Self> {
                    unsafe { NodePos::new_unchecked(Self::Raw::search(&keys.0, search)) }
                }

                type Stack = Stack<Self, { max_height::<Self>() }>;
            }

            impl BTreeKey for nonmax::$nonmax {
                type Int = Self;

                #[inline]
                fn to_int(self) -> Self::Int {
                    self
                }

                #[inline]
                fn from_int(int: Self::Int) -> Self {
                    int
                }
            }
        )*
    };
}

impl_int! {
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
