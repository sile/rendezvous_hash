use crate::node::{Node, WithHashCode};
use std::slice;
use std::vec;

pub fn iter<'a, T: Node>(iter: slice::Iter<'a, WithHashCode<T>>) -> Iter<'a, T> {
    Iter(iter)
}

/// An iterator over the nodes of a candidate set.
pub struct Iter<'a, T: 'a + Node>(slice::Iter<'a, WithHashCode<T>>);
impl<'a, T: 'a + Node> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| &n.node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub fn into_iter<T: Node>(iter: vec::IntoIter<WithHashCode<T>>) -> IntoIter<T> {
    IntoIter(iter)
}

/// An owning iterator over the nodes of a candidate set.
pub struct IntoIter<T: Node>(vec::IntoIter<WithHashCode<T>>);
impl<T: Node> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| n.node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
