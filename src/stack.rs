//! Stack used for mutable tree operations that records a path through the tree.

use core::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use crate::{
    BTreeInteger, NodeRef,
    node::NodePos,
    node::{MAX_POOL_SIZE, node_layout},
};

/// Returns the worst case maximum height for a tree with key `I`.
#[inline]
pub(crate) const fn max_height<I: BTreeInteger>() -> usize {
    // Get the maximum possible number of leaf nodes, assuming an empty `V`.
    //
    // `NodePool` stores offsets in a u32 and therefore the total pool size
    // cannot exceed `u32::MAX`.
    let mut nodes = MAX_POOL_SIZE / node_layout::<I, ()>().0.size();
    let mut height = 0;

    // If there are multiple nodes at this height then we need another level
    // above it.
    while nodes > 1 {
        height += 1;

        // If there are less than B nodes then we just need a single root node
        // above it which will never get split.
        if nodes < I::B {
            break;
        }

        // Otherwise assume a worst case with all internal nodes being half-full.
        nodes = nodes.div_ceil(I::B / 2);
    }

    height
}

/// A height in the tree.
///
/// This has the invariant of always being less than `max_height::<I>()`, which
/// allows safe unchecked indexing in a stack.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Height<I: BTreeInteger> {
    height: usize,
    marker: PhantomData<fn() -> I>,
}

impl<I: BTreeInteger> Height<I> {
    /// Returns the height for leaf nodes.
    #[inline]
    pub(crate) fn leaf() -> Self {
        Self {
            height: 0,
            marker: PhantomData,
        }
    }
    /// Returns the maximum possible height for a tree.
    #[inline]
    pub(crate) fn max() -> Self {
        Self {
            height: max_height::<I>(),
            marker: PhantomData,
        }
    }

    /// Returns one level down (towards the leaves).
    #[inline]
    pub(crate) fn down(self) -> Option<Self> {
        if self.height == 0 {
            None
        } else {
            Some(Self {
                height: self.height - 1,
                marker: PhantomData,
            })
        }
    }

    /// Returns one level up (towards the root) up to the given maximum heigh.
    #[inline]
    pub(crate) fn up(self, max: Height<I>) -> Option<Self> {
        if self.height >= max.height {
            None
        } else {
            Some(Self {
                height: self.height + 1,
                marker: PhantomData,
            })
        }
    }
}

/// Stack which holds the path to a leaf node from the root of the tree.
///
/// The is large enough to hold `max_height::<I>()`, which depends on the branching
/// factor and the node size.
///
/// The stack is indexed with `Height` which allows unchecked indexing since
/// all heights must be less than `max_heigh::<I>()`.
#[derive(Clone)]
pub(crate) struct Stack<I: BTreeInteger, const H: usize> {
    entries: [(NodeRef, NodePos<I>); H],
}

impl<I: BTreeInteger, const H: usize> Default for Stack<I, H> {
    #[inline]
    fn default() -> Self {
        Self {
            // The values here don't matter and zero initialization is slightly
            // faster.
            entries: [(NodeRef::zero(), NodePos::zero()); H],
        }
    }
}

impl<I: BTreeInteger, const H: usize> Index<Height<I>> for Stack<I, H> {
    type Output = (NodeRef, NodePos<I>);

    #[inline]
    fn index(&self, index: Height<I>) -> &Self::Output {
        const { assert!(H == max_height::<I>()) };
        unsafe { self.entries.get_unchecked(index.height) }
    }
}

impl<I: BTreeInteger, const H: usize> IndexMut<Height<I>> for Stack<I, H> {
    #[inline]
    fn index_mut(&mut self, index: Height<I>) -> &mut Self::Output {
        const { assert!(H == max_height::<I>()) };
        unsafe { self.entries.get_unchecked_mut(index.height) }
    }
}
