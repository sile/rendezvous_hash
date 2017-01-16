use std::hash::Hash;

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
impl<T: Hash> Node<(T, Capacity)> {
    pub fn update_hash_with_capacity<H, U: Hash>(&mut self,
                                                 hasher: &H,
                                                 item: &U,
                                                 capacity: Capacity)
        where H: for<'a> NodeHasher<(&'a T, u16)>
    {
        let hash = (0..capacity.0).map(|i| hasher.hash(&(&self.node.0, i), item)).max().unwrap();
        self.hash = hash;
    }
}
