//! An implementation of Rendezvous (a.k.a, highest random weight) hashing algorithm.
//!
//! # References
//!
//! - [Rendezvous hashing (Wikipedia)](https://en.wikipedia.org/wiki/Rendezvous_hashing)
//! - [Weighted Distributed Hash Tables]
//!   (https://pdfs.semanticscholar.org/8c55/282dc37d1e3b46b15c2d97f60568ccb9c9cd.pdf)
//!    - This paper describes an efficient method for
//!      calculating consistent hash values for heterogeneous nodes.
//!
//! # Examples
//!
//! For homogeneous nodes:
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
//!
//! For heterogeneous nodes:
//!
//! ```
//! use std::collections::HashMap;
//! use rendezvous_hash::RendezvousNodes;
//! use rendezvous_hash::{WeightedNode, Capacity};
//!
//! let mut nodes = RendezvousNodes::default();
//! nodes.insert(WeightedNode::new("foo", Capacity::new(70.0).unwrap()));
//! nodes.insert(WeightedNode::new("bar", Capacity::new(20.0).unwrap()));
//! nodes.insert(WeightedNode::new("baz", Capacity::new(9.0).unwrap()));
//! nodes.insert(WeightedNode::new("qux", Capacity::new(1.0).unwrap()));
//!
//! let mut counts = HashMap::new();
//! for item in 0..10000 {
//!     let node = nodes.calc_candidates(&item).nth(0).unwrap();
//!     *counts.entry(node.node.to_string()).or_insert(0) += 1;
//! }
//! assert_eq!(((counts["foo"] as f64) / 100.0).round(), 70.0);
//! assert_eq!(((counts["bar"] as f64) / 100.0).round(), 20.0);
//! assert_eq!(((counts["baz"] as f64) / 100.0).round(), 9.0);
//! assert_eq!(((counts["qux"] as f64) / 100.0).round(), 1.0);
//! ```
#![warn(missing_docs)]
extern crate siphasher;

use std::borrow::Borrow;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub use node::{Capacity, IdNode, KeyValueNode, Node, WeightedNode};

mod iterators_impl;
mod node;

pub mod iterators {
    //! `Iterator` trait implementations.

    pub use crate::iterators_impl::Candidates;
    pub use crate::iterators_impl::IntoIter;
    pub use crate::iterators_impl::Iter;
}

pub mod types {
    //! Miscellaneous types.

    pub use crate::node::SignPositiveF64;
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
pub struct DefaultNodeHasher(());
impl DefaultNodeHasher {
    /// Makes a new `DefaultNodeHasher` instance.
    pub fn new() -> Self {
        DefaultNodeHasher(())
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
pub struct RendezvousNodes<N: Node, H> {
    nodes: Vec<node::WithHashCode<N>>,
    hasher: H,
}
impl<N, H> RendezvousNodes<N, H>
where
    N: Node,
    H: NodeHasher<N::NodeId>,
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
        for n in self.nodes.iter_mut() {
            let code = n.node.hash_code(hasher, &item);
            n.hash_code = Some(code);
        }
        self.nodes.sort_by(|a, b| {
            (&b.hash_code, b.node.node_id()).cmp(&(&a.hash_code, a.node.node_id()))
        });
        iterators_impl::candidates(self.nodes.iter())
    }

    /// Returns the candidate nodes for `item`.
    ///
    /// The higher priority node is located in front of the returned candidate sequence.
    ///
    /// Note that this method takes `O(n log n)` steps
    /// (where `n` is the return value of `self.len()`).
    ///
    /// This is equivalent to `calc_candidates` method except this allocates
    /// `n * (size_of<usize>() + size_of<N::HashCode>())` memory internally.
    pub fn calc_candidates_immut<T: Hash>(&self, item: &T) -> impl Iterator<Item = &N> {
        let hasher = &self.hasher;
        let mut nodes = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let code = n.node.hash_code(hasher, &item);
            nodes.push(node::WithHashCode {
                node: &n.node,
                hash_code: Some(code),
            });
        }
        nodes.sort_by(|a, b| {
            (&b.hash_code, b.node.node_id()).cmp(&(&a.hash_code, a.node.node_id()))
        });
        nodes.into_iter().map(|n| n.node)
    }
}
impl<N: Node, H> RendezvousNodes<N, H> {
    /// Inserts a new candidate node.
    ///
    /// If a node which has an identifier equal to `node` exists,
    /// it will be removed and returned as `Some(N)`.
    pub fn insert(&mut self, node: N) -> Option<N> {
        let old = self.remove(node.node_id());
        self.nodes.push(node::WithHashCode::new(node));
        old
    }

    /// Removes the specified node from the candidates.
    ///
    /// If the node does not exist, this method will return `None`.
    pub fn remove<M>(&mut self, node_id: &M) -> Option<N>
    where
        N::NodeId: Borrow<M>,
        M: PartialEq,
    {
        if let Some(i) = self
            .nodes
            .iter()
            .position(|n| n.node.node_id().borrow() == node_id)
        {
            Some(self.nodes.swap_remove(i).node)
        } else {
            None
        }
    }

    /// Returns `true` if the specified node exists in this candidate set, otherwise `false`.
    pub fn contains<M>(&self, node_id: &M) -> bool
    where
        N::NodeId: Borrow<M>,
        M: PartialEq,
    {
        self.nodes
            .iter()
            .any(|n| n.node.node_id().borrow() == node_id)
    }

    /// Returns the count of the candidate nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns an iterator over the nodes of this candidate set.
    pub fn iter(&self) -> iterators::Iter<N> {
        iterators_impl::iter(self.nodes.iter())
    }
}
impl<N: Node> Default for RendezvousNodes<N, DefaultNodeHasher> {
    fn default() -> Self {
        Self::new(DefaultNodeHasher::new())
    }
}
impl<N: Node, H> IntoIterator for RendezvousNodes<N, H> {
    type Item = N;
    type IntoIter = iterators::IntoIter<N>;
    fn into_iter(self) -> Self::IntoIter {
        iterators_impl::into_iter(self.nodes.into_iter())
    }
}
impl<N: Node, H> Extend<N> for RendezvousNodes<N, H> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = N>,
    {
        for n in iter {
            let _ = self.insert(n);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    macro_rules! assert_calc_candidates {
        ($nodes:expr, $key:expr, $candidates:expr) => {
            assert_eq!(
                $nodes.calc_candidates($key).collect::<Vec<_>>(),
                $candidates
            );
            assert_eq!(
                $nodes.calc_candidates_immut($key).collect::<Vec<_>>(),
                $candidates
            );
        };
    }

    #[test]
    fn it_works() {
        let mut nodes = RendezvousNodes::default();
        nodes.insert("foo");
        nodes.insert("bar");
        nodes.insert("baz");
        nodes.insert("qux");
        assert_calc_candidates!(nodes, &1, [&"bar", &"baz", &"foo", &"qux"]);
        assert_calc_candidates!(nodes, &"key", [&"qux", &"bar", &"foo", &"baz"]);

        nodes.remove(&"baz");
        assert_calc_candidates!(nodes, &1, [&"bar", &"foo", &"qux"]);
        assert_calc_candidates!(nodes, &"key", [&"qux", &"bar", &"foo"]);

        nodes.remove(&"bar");
        assert_calc_candidates!(nodes, &1, [&"foo", &"qux"]);
        assert_calc_candidates!(nodes, &"key", [&"qux", &"foo"]);

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
    fn kv_nodes() {
        let mut nodes = RendezvousNodes::default();
        nodes.insert(KeyValueNode::new("foo", ()));
        nodes.insert(KeyValueNode::new("bar", ()));
        nodes.insert(KeyValueNode::new("baz", ()));
        nodes.insert(KeyValueNode::new("qux", ()));
        assert_eq!(
            nodes
                .calc_candidates(&1)
                .map(|n| &n.key)
                .collect::<Vec<_>>(),
            [&"bar", &"baz", &"foo", &"qux"]
        );
        assert_eq!(
            nodes
                .calc_candidates(&"key")
                .map(|n| &n.key)
                .collect::<Vec<_>>(),
            [&"qux", &"bar", &"foo", &"baz"]
        );
    }

    #[test]
    fn heterogeneous_nodes() {
        let mut nodes = RendezvousNodes::default();
        nodes.insert(WeightedNode::new("foo", Capacity::new(70.0).unwrap()));
        nodes.insert(WeightedNode::new("bar", Capacity::new(20.0).unwrap()));
        nodes.insert(WeightedNode::new("baz", Capacity::new(9.0).unwrap()));
        nodes.insert(WeightedNode::new("qux", Capacity::new(1.0).unwrap()));

        let mut counts = HashMap::new();
        for item in 0..10000 {
            let node = nodes.calc_candidates(&item).nth(0).unwrap();
            *counts.entry(node.node.to_string()).or_insert(0) += 1;
        }
        assert_eq!(((counts["foo"] as f64) / 100.0).round(), 70.0);
        assert_eq!(((counts["bar"] as f64) / 100.0).round(), 20.0);
        assert_eq!(((counts["baz"] as f64) / 100.0).round(), 9.0);
        assert_eq!(((counts["qux"] as f64) / 100.0).round(), 1.0);
    }
}
