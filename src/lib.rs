use std::hash::{Hash, Hasher, BuildHasher};
use std::hash::BuildHasherDefault;
use std::collections::hash_map::DefaultHasher;
use std::borrow::Borrow;
use std::slice;
use std::iter;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Weight(f64);
impl Weight {
    pub fn new(weight: f64) -> Option<Self> {
        if 0.0 < weight && weight <= 1.0 {
            Some(Weight(weight))
        } else {
            None
        }
    }
    pub fn as_f64(&self) -> f64 {
        self.0
    }
}

pub trait Point: PartialEq + Hash {
    fn hash_with_item<T: Hash, H: Hasher>(&self, item: &T, hasher: &mut H) {
        item.hash(hasher);
        self.hash(hasher);
    }
    fn weight(&self) -> Weight {
        Weight(1.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlainPoint<P>(P);
impl<P: PartialEq + Hash> PlainPoint<P> {
    pub fn new(inner: P) -> Self {
        PlainPoint(inner)
    }
    pub fn into_inner(self) -> P {
        self.0
    }
}
impl<P: PartialEq + Hash> Point for PlainPoint<P> {}

impl Point for i8 {}
impl Point for u8 {}
impl Point for i16 {}
impl Point for u16 {}
impl Point for i32 {}
impl Point for u32 {}
impl Point for i64 {}
impl Point for u64 {}
impl<'a> Point for &'a str {}
impl Point for String {}
impl<'a> Point for &'a [u8] {}
impl Point for Vec<u8> {}

#[derive(Debug, Clone)]
pub struct RendezvousPoints<P, H> {
    points: Vec<P>,
    hasher: H,
}
impl<P, H> RendezvousPoints<P, H>
    where P: Point,
          H: BuildHasher
{
    pub fn new(hasher: H) -> Self {
        RendezvousPoints {
            points: Vec::new(),
            hasher: hasher,
        }
    }
    pub fn insert(&mut self, point: P) -> Option<P> {
        let old = self.remove(&point);
        self.points.push(point);
        old
    }
    pub fn remove<Q>(&mut self, point: &Q) -> Option<P>
        where P: Borrow<Q>,
              Q: PartialEq
    {
        if let Some(i) = self.points.iter().position(|p| p.borrow() == point) {
            Some(self.points.swap_remove(i))
        } else {
            None
        }
    }
    pub fn calc_candidates<T: Hash>(&mut self, item: &T) -> Candidates<P> {
        let builder = &self.hasher;
        self.points.sort_by_key(|p| {
            let mut hasher = builder.build_hasher();
            p.hash_with_item(item, &mut hasher);
            ((hasher.finish() as f64) * p.weight().0) as u64
        });
        Candidates(self.points.iter().rev())
    }
}
impl<P> Default for RendezvousPoints<P, BuildHasherDefault<DefaultHasher>>
    where P: Point
{
    fn default() -> Self {
        Self::new(BuildHasherDefault::default())
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut points = RendezvousPoints::default();
        points.insert("foo");
        points.insert("bar");
        points.insert("baz");
        assert_eq!(points.calc_candidates(&1).collect::<Vec<_>>(), [&"foo"]);
    }
}
