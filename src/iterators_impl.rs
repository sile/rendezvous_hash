use std::iter;
use std::slice;

pub fn candidates<'a, P: 'a>(inner: iter::Rev<slice::Iter<'a, P>>) -> Candidates<P> {
    Candidates(inner)
}

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
