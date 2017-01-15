//! An implementation of Rendezvous (a.k.a, highest random weight) hashing algorithm.
//!
//! Reference: [Rendezvous hashing (Wikipedia)](https://en.wikipedia.org/wiki/Rendezvous_hashing)
//!
//! # Examples
//!
//! ```
//! use rendezvous_hash::RendezvousNodes;
//!
//! // Constructs a node (a.k.a., server, site, etc) set.
//! let mut nodes = RendezvousNodes::default();
//! nodes.insert("foo");
//! nodes.insert("bar");
//! nodes.insert("baz");
//! nodes.insert("qux");
//!
//! // Finds candidate nodes for an item (a.k.a., object).
//! assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
//!            [&"bar", &"baz", &"foo", &"qux"]);
//! assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
//!            [&"qux", &"bar", &"foo", &"baz"]);
//!
//! // Update the node set.
//! // (The relative order between existing nodes are preserved)
//! nodes.remove(&"baz");
//! assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
//!            [&"bar", &"foo", &"qux"]);
//! assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
//!            [&"qux", &"bar", &"foo"]);
//! ```
#![warn(missing_docs)]
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;
use std::borrow::Borrow;

mod iterators_impl;

pub mod iterators {
    //! `Iterator` trait implementations.

    pub use iterators_impl::Iter;
    pub use iterators_impl::IntoIter;
    pub use iterators_impl::Candidates;
}

/// This trait allows calculating the hash value of a node for a specific item.
pub trait NodeHasher<N> {
    /// Returns the hash value for the combination of `node` and `item`.
    fn hash<T: Hash>(&self, node: &N, item: &T) -> u64;
}

/// The default `NodeHasher` implementation.
///
/// This uses `DefaultHasher` to hash nodes and items.
/// `DefaultHasher` is provided by Rust standard library.
///
/// To hash a combination of a node and an item,
/// `DefaultNodeHasher` hashes the item at first,
/// then hashes the node,
/// and finally returns the resulting hash value
/// (as follows).
///
/// ```no_run
/// use std::collections::hash_map::DefaultHasher;
/// # use std::hash::{Hash, Hasher};
/// # let item = ();
/// # let node = ();
///
/// let mut hasher = DefaultHasher::new();
/// item.hash(&mut hasher);
/// node.hash(&mut hasher);
/// hasher.finish()
/// # ;
/// ```
#[derive(Debug, Clone)]
pub struct DefaultNodeHasher {
    _dummy: (),
}
impl DefaultNodeHasher {
    /// Makes a new `DefaultNodeHasher` instance.
    pub fn new() -> Self {
        DefaultNodeHasher { _dummy: () }
    }
}
impl<N: Hash> NodeHasher<N> for DefaultNodeHasher {
    fn hash<T: Hash>(&self, node: &N, item: &T) -> u64 {
        let mut hasher = DefaultHasher::new();
        item.hash(&mut hasher);
        node.hash(&mut hasher);
        hasher.finish()
    }
}

/// A candidate node set of a rendezvous for clients that are requiring the same item.
///
/// # Examples
///
/// ```
/// use rendezvous_hash::RendezvousNodes;
///
/// // Constructs a node (a.k.a., server, site, etc) set.
/// let mut nodes = RendezvousNodes::default();
/// nodes.insert("foo");
/// nodes.insert("bar");
/// nodes.insert("baz");
/// nodes.insert("qux");
///
/// // Finds candidate nodes for an item (a.k.a., object).
/// assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
///            [&"bar", &"baz", &"foo", &"qux"]);
/// assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
///            [&"qux", &"bar", &"foo", &"baz"]);
///
/// // Update the node set.
/// // (The relative order between existing nodes are preserved)
/// nodes.remove(&"baz");
/// assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
///            [&"bar", &"foo", &"qux"]);
/// assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
///            [&"qux", &"bar", &"foo"]);
/// ```
#[derive(Debug, Clone)]
pub struct RendezvousNodes<N, H> {
    nodes: Vec<N>,
    hasher: H,
}
impl<N, H> RendezvousNodes<N, H>
    where N: PartialEq + Hash,
          H: NodeHasher<N>
{
    /// Makes a new `RendezvousNodes` instance.
    pub fn new(hasher: H) -> Self {
        RendezvousNodes {
            nodes: Vec::new(),
            hasher: hasher,
        }
    }

    /// Returns the candidate nodes for `item`.
    ///
    /// The higher priority node is located in front of the returned candidate sequence.
    ///
    /// Note that this method takes `O(n log n)` steps
    /// (where `n` is the return value of `self.len()`).
    pub fn calc_candidates<T: Hash>(&mut self, item: &T) -> iterators::Candidates<N> {
        let hasher = &self.hasher;
        self.nodes.sort_by_key(|n| hasher.hash(n, item));
        iterators_impl::candidates(self.nodes.iter().rev())
    }
}
impl<N, H> RendezvousNodes<N, H>
    where N: PartialEq + Hash
{
    /// Inserts a new candidate node.
    ///
    /// If a node which equals to `node` exists, it will be removed and returned as `Some(N)`.
    pub fn insert(&mut self, node: N) -> Option<N> {
        let old = self.remove(&node);
        self.nodes.push(node);
        old
    }

    /// Removes the specified node from the candidates.
    ///
    /// If the node does not exist, this method will return `None`.
    pub fn remove<M>(&mut self, node: &M) -> Option<N>
        where N: Borrow<M>,
              M: PartialEq
    {
        if let Some(i) = self.nodes.iter().position(|n| n.borrow() == node) {
            Some(self.nodes.swap_remove(i))
        } else {
            None
        }
    }

    /// Returns `true` if the specified node exists in this candidate set, otherwise `false`.
    pub fn contains<M>(&self, node: &M) -> bool
        where N: Borrow<M>,
              M: PartialEq
    {
        self.nodes.iter().any(|n| n.borrow() == node)
    }
}
impl<N, H> RendezvousNodes<N, H> {
    /// Returns the count of the candidate nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns an iterator over the nodes of this candidate set.
    pub fn iter(&self) -> iterators::Iter<N> {
        iterators_impl::iter(self.nodes.iter())
    }
}
impl<N> Default for RendezvousNodes<N, DefaultNodeHasher>
    where N: PartialEq + Hash
{
    fn default() -> Self {
        Self::new(DefaultNodeHasher::new())
    }
}
impl<N, H> IntoIterator for RendezvousNodes<N, H> {
    type Item = N;
    type IntoIter = iterators::IntoIter<N>;
    fn into_iter(self) -> Self::IntoIter {
        iterators_impl::into_iter(self.nodes.into_iter())
    }
}
impl<N, H> Extend<N> for RendezvousNodes<N, H>
    where N: PartialEq + Hash
{
    fn extend<T>(&mut self, iter: T)
        where T: IntoIterator<Item = N>
    {
        for n in iter {
            let _ = self.insert(n);
        }
    }
}

/// The capacity of a node.
///
/// "capacity" is a virtual value indicating
/// the resource amount of a node.
///
/// For example, if the capacity of a node is twice the other,
/// the former may be selected by items twice as many times as the latter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Capacity(u16);
impl Capacity {
    /// Makes a new `Capacity` instance.
    ///
    /// Note that `capacity` must be a non zero value.
    /// If `0` is passed, this method will returns `None`.
    pub fn new(capacity: u16) -> Option<Self> {
        if capacity == 0 {
            None
        } else {
            Some(Capacity(capacity))
        }
    }

    /// Returns the value of this instance.
    pub fn value(&self) -> u16 {
        self.0
    }
}

/// A heterogeneous candidate node set of a rendezvous for clients that are requiring the same item.
///
/// "heterogeneous" means that each node can have a different capacity.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
/// use rendezvous_hash::Capacity;
/// use rendezvous_hash::HeterogeneousRendezvousNodes;
///
/// let mut nodes = HeterogeneousRendezvousNodes::default();
/// nodes.insert("foo", Capacity::new(70).unwrap());
/// nodes.insert("bar", Capacity::new(20).unwrap());
/// nodes.insert("baz", Capacity::new(9).unwrap());
/// nodes.insert("qux", Capacity::new(1).unwrap());
///
/// let mut counts = HashMap::new();
/// for item in 0..10000 {
///     let node = nodes.calc_candidates(&item).nth(0).unwrap();
///     *counts.entry(node.0.to_string()).or_insert(0) += 1;
/// }
/// assert_eq!(((counts["foo"] as f64) / 100.0).round(), 70.0);
/// assert_eq!(((counts["bar"] as f64) / 100.0).round(), 20.0);
/// assert_eq!(((counts["baz"] as f64) / 100.0).round(), 9.0);
/// assert_eq!(((counts["qux"] as f64) / 100.0).round(), 1.0);
/// ```
#[derive(Debug, Clone)]
pub struct HeterogeneousRendezvousNodes<N, H> {
    nodes: Vec<(N, Capacity)>,
    hasher: H,
}
impl<N, H> HeterogeneousRendezvousNodes<N, H>
    where N: PartialEq + Hash,
          H: for<'a> NodeHasher<(&'a N, u16)>
{
    /// Makes a new `HeterogeneousRendezvousNodes` instance.
    pub fn new(hasher: H) -> Self {
        HeterogeneousRendezvousNodes {
            nodes: Vec::new(),
            hasher: hasher,
        }
    }

    /// Returns the candidate nodes for `item`.
    ///
    /// The higher priority node is located in front of the returned candidate sequence.
    ///
    /// Note that this method takes `O(n * m + n log n)` steps
    /// (where `n` is the return value of `self.len()` and
    /// `m` is the maximum value among the capacities of the nodes.)
    pub fn calc_candidates<T: Hash>(&mut self, item: &T) -> iterators::Candidates<(N, Capacity)> {
        let hasher = &self.hasher;
        self.nodes.sort_by_key(|&(ref n, capacity)| {
            (0..capacity.0)
                .map(|i| hasher.hash(&(n, i), item))
                .max()
                .unwrap()
        });
        iterators_impl::candidates(self.nodes.iter().rev())
    }
}
impl<N, H> HeterogeneousRendezvousNodes<N, H>
    where N: PartialEq + Hash
{
    /// Inserts a new candidate node which has the capacity `capacity`.
    ///
    /// If a node which equals to `node` exists,
    /// it will be removed and returned as `Some((N, Capacity))`.
    pub fn insert(&mut self, node: N, capacity: Capacity) -> Option<(N, Capacity)> {
        let old = self.remove(&node);
        self.nodes.push((node, capacity));
        old
    }

    /// Removes the specified node from the candidates.
    ///
    /// If the node does not exist, this method will return `None`.
    pub fn remove<M>(&mut self, node: &M) -> Option<(N, Capacity)>
        where N: Borrow<M>,
              M: PartialEq
    {
        if let Some(i) = self.nodes.iter().position(|n| n.0.borrow() == node) {
            Some(self.nodes.swap_remove(i))
        } else {
            None
        }
    }

    /// Returns `true` if the specified node exists in this candidate set, otherwise `false`.
    pub fn contains<M>(&self, node: &M) -> bool
        where N: Borrow<M>,
              M: PartialEq
    {
        self.nodes.iter().any(|n| n.0.borrow() == node)
    }
}
impl<N, H> HeterogeneousRendezvousNodes<N, H> {
    /// Returns the count of the candidate nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns an iterator over the nodes of this candidate set.
    pub fn iter(&self) -> iterators::Iter<(N, Capacity)> {
        iterators_impl::iter(self.nodes.iter())
    }
}
impl<N> Default for HeterogeneousRendezvousNodes<N, DefaultNodeHasher>
    where N: PartialEq + Hash
{
    fn default() -> Self {
        Self::new(DefaultNodeHasher::new())
    }
}
impl<N, H> IntoIterator for HeterogeneousRendezvousNodes<N, H> {
    type Item = (N, Capacity);
    type IntoIter = iterators::IntoIter<(N, Capacity)>;
    fn into_iter(self) -> Self::IntoIter {
        iterators_impl::into_iter(self.nodes.into_iter())
    }
}
impl<N, H> Extend<(N, Capacity)> for HeterogeneousRendezvousNodes<N, H>
    where N: PartialEq + Hash
{
    fn extend<T>(&mut self, iter: T)
        where T: IntoIterator<Item = (N, Capacity)>
    {
        for (n, c) in iter {
            let _ = self.insert(n, c);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use super::*;

    #[test]
    fn it_works() {
        let mut nodes = RendezvousNodes::default();
        nodes.insert("foo");
        nodes.insert("bar");
        nodes.insert("baz");
        nodes.insert("qux");
        assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"bar", &"baz", &"foo", &"qux"]);
        assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"bar", &"foo", &"baz"]);

        nodes.remove(&"baz");
        assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"bar", &"foo", &"qux"]);
        assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"bar", &"foo"]);

        nodes.remove(&"bar");
        assert_eq!(nodes.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"foo", &"qux"]);
        assert_eq!(nodes.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"foo"]);

        nodes.insert("bar");
        nodes.insert("baz");
        let mut counts = HashMap::new();
        for item in 0..1000 {
            let node = nodes.calc_candidates(&item).nth(0).unwrap();
            *counts.entry(node.to_string()).or_insert(0) += 1;
        }
        assert_eq!(counts["foo"], 246);
        assert_eq!(counts["bar"], 266);
        assert_eq!(counts["baz"], 237);
        assert_eq!(counts["qux"], 251);
    }

    #[test]
    fn heterogeneous_nodes() {
        let mut nodes = HeterogeneousRendezvousNodes::default();
        nodes.insert("foo", Capacity::new(70).unwrap());
        nodes.insert("bar", Capacity::new(20).unwrap());
        nodes.insert("baz", Capacity::new(9).unwrap());
        nodes.insert("qux", Capacity::new(1).unwrap());

        let mut counts = HashMap::new();
        for item in 0..10000 {
            let node = nodes.calc_candidates(&item).nth(0).unwrap();
            *counts.entry(node.0.to_string()).or_insert(0) += 1;
        }
        assert_eq!(((counts["foo"] as f64) / 100.0).round(), 70.0);
        assert_eq!(((counts["bar"] as f64) / 100.0).round(), 20.0);
        assert_eq!(((counts["baz"] as f64) / 100.0).round(), 9.0);
        assert_eq!(((counts["qux"] as f64) / 100.0).round(), 1.0);
    }
}
