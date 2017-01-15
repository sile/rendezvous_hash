use std::iter;
use std::slice;

pub fn candidates<'a, P: 'a>(inner: iter::Rev<slice::Iter<'a, P>>) -> Candidates<P> {
    Candidates(inner)
}

/// An iterator which represents a sequence of the candidate nodes for a rendezvous.
///
/// The higher priority node is placed in front of this sequence.
pub struct Candidates<'a, P: 'a>(iter::Rev<slice::Iter<'a, P>>);
impl<'a, P: 'a> Iterator for Candidates<'a, P> {
    type Item = &'a P;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
