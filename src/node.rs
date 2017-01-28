use std::hash::{Hash, Hasher};
use std::cmp;

use super::{Capacity, NodeHasher};

#[derive(Debug, Clone)]
pub struct Node<T> {
    pub node: T,
    pub hash: u64,
}
impl<T> Node<T> {
    pub fn new(node: T) -> Self {
        Node {
            node: node,
            hash: 0,
        }
    }
}
impl<T: Hash> Node<T> {
    pub fn update_hash<H: NodeHasher<T>, U: Hash>(&mut self, hasher: &H, item: &U) {
        let hash = hasher.hash(&self.node, item);
        self.hash = hash;
    }
}

#[derive(Debug, Clone)]
pub struct WeightedNode<T> {
    pub node: T,
    pub capacity: Capacity,
    pub hash: f64,
}
impl<T> WeightedNode<T> {
    pub fn new(node: T, capacity: Capacity) -> Self {
        WeightedNode {
            node: node,
            capacity: capacity,
            hash: 0.0,
        }
    }
}
impl<T: Hash> WeightedNode<T> {
    pub fn update_hash<H: NodeHasher<T>, U: Hash>(&mut self, hasher: &H, item: &U) {
        // Uses "Logarithmic Method" described in "Weighted Distributed Hash Tables"
        use std::u64::MAX;
        let hash = hasher.hash(&self.node, item) as f64;
        let distance = (hash / MAX as f64).ln();
        self.hash = distance / self.capacity.value() as f64;
    }
}
impl<T> WeightedNode<T> {
    pub fn into_tuple(self) -> (T, Capacity) {
        (self.node, self.capacity)
    }
}

/// Key-Value node.
///
/// Only key is used for calculating the hash value of a node.
#[derive(Debug, Clone)]
pub struct KeyValueNode<K, V> {
    /// The key of this node.
    pub key: K,

    /// The value of this node.
    pub value: V,
}
impl<K, V> KeyValueNode<K, V>
    where K: Hash + Ord + PartialEq
{
    /// Makes a new `KeyValueNode` instance.
    pub fn new(key: K, value: V) -> Self {
        KeyValueNode {
            key: key,
            value: value,
        }
    }
}
impl<K: Hash, V> Hash for KeyValueNode<K, V> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.key.hash(hasher);
    }
}
impl<K: PartialEq, V> PartialEq for KeyValueNode<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl<K: PartialEq, V> Eq for KeyValueNode<K, V> {}
impl<K: PartialOrd, V> PartialOrd for KeyValueNode<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.key.partial_cmp(&other.key)
    }
}
impl<K: Ord, V> Ord for KeyValueNode<K, V> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.key.cmp(&other.key)
    }
}
