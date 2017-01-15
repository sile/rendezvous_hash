use std::vec;
use std::iter;
use std::slice;

pub fn iter<'a, T>(iter: slice::Iter<'a, T>) -> Iter<'a, T> {
    Iter(iter)
}

/// An iterator over the nodes of a candidate set.
pub struct Iter<'a, T: 'a>(slice::Iter<'a, T>);
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub fn into_iter<T>(iter: vec::IntoIter<T>) -> IntoIter<T> {
    IntoIter(iter)
}

/// An owning iterator over the nodes of a candidate set.
pub struct IntoIter<T>(vec::IntoIter<T>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub fn candidates<'a, T: 'a>(inner: iter::Rev<slice::Iter<'a, T>>) -> Candidates<T> {
    Candidates(inner)
}

/// An iterator which represents a sequence of the candidate nodes for a rendezvous.
///
/// The higher priority node is placed in front of this sequence.
pub struct Candidates<'a, T: 'a>(iter::Rev<slice::Iter<'a, T>>);
impl<'a, T: 'a> Iterator for Candidates<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
