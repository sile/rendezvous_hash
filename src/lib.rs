use std::hash::{Hash, Hasher, BuildHasher};
use std::hash::BuildHasherDefault;
use std::collections::hash_map::DefaultHasher;
use std::borrow::Borrow;
use std::slice;
use std::iter;


#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Capacity(u8);
impl Capacity {
    pub fn new(capacity: u8) -> Option<Self> {
        if capacity == 0 {
            None
        } else {
            Some(Capacity(capacity))
        }
    }
}

#[derive(Debug, Clone)]
pub struct RendezvousPoints<P, H> {
    points: Vec<P>,
    hasher: H,
}
impl<P, H> RendezvousPoints<P, H>
    where P: PartialEq + Hash,
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
    pub fn hasher(&self) -> H::Hasher {
        self.hasher.build_hasher()
    }
    pub fn calc_candidates<T: Hash>(&mut self, item: &T) -> Candidates<P> {
        let builder = &self.hasher;
        self.points.sort_by_key(|p| {
            let mut hasher = builder.build_hasher();
            (item, p).hash(&mut hasher);
            hasher.finish()
        });
        Candidates(self.points.iter().rev())
    }
}
impl<P> Default for RendezvousPoints<P, BuildHasherDefault<DefaultHasher>>
    where P: PartialEq + Hash
{
    fn default() -> Self {
        Self::new(BuildHasherDefault::default())
    }
}

#[derive(Debug, Clone)]
pub struct NonUniformRendezvousPoints<P, H> {
    points: Vec<(P, Capacity)>,
    hasher: H,
}
impl<P, H> NonUniformRendezvousPoints<P, H>
    where P: PartialEq + Hash,
          H: BuildHasher
{
    pub fn new(hasher: H) -> Self {
        NonUniformRendezvousPoints {
            points: Vec::new(),
            hasher: hasher,
        }
    }
    pub fn insert(&mut self, point: P, capacity: Capacity) -> Option<(P, Capacity)> {
        let old = self.remove(&point);
        self.points.push((point, capacity));
        old
    }
    pub fn remove<Q>(&mut self, point: &Q) -> Option<(P, Capacity)>
        where P: Borrow<Q>,
              Q: PartialEq
    {
        if let Some(i) = self.points.iter().position(|p| p.0.borrow() == point) {
            Some(self.points.swap_remove(i))
        } else {
            None
        }
    }
    pub fn hasher(&self) -> H::Hasher {
        self.hasher.build_hasher()
    }
    pub fn calc_candidates<T: Hash>(&mut self, item: &T) -> Candidates<(P, Capacity)> {
        let builder = &self.hasher;
        self.points.sort_by_key(|&(ref p, capacity)| {
            (0..capacity.0)
                .map(|i| {
                    let mut hasher = builder.build_hasher();
                    (item, p, i).hash(&mut hasher);
                    hasher.finish()
                })
                .max()
                .unwrap()
        });
        Candidates(self.points.iter().rev())
    }
}
impl<P> Default for NonUniformRendezvousPoints<P, BuildHasherDefault<DefaultHasher>>
    where P: PartialEq + Hash
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
    use std::collections::HashMap;
    use super::*;

    #[test]
    fn it_works() {
        let mut points = RendezvousPoints::default();
        points.insert("foo");
        points.insert("bar");
        points.insert("baz");
        points.insert("qux");
        assert_eq!(points.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"bar", &"baz", &"foo", &"qux"]);
        assert_eq!(points.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"bar", &"foo", &"baz"]);

        points.remove(&"baz");
        assert_eq!(points.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"bar", &"foo", &"qux"]);
        assert_eq!(points.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"bar", &"foo"]);

        points.remove(&"bar");
        assert_eq!(points.calc_candidates(&1).collect::<Vec<_>>(),
                   [&"foo", &"qux"]);
        assert_eq!(points.calc_candidates(&"key").collect::<Vec<_>>(),
                   [&"qux", &"foo"]);

        points.insert("bar");
        points.insert("baz");
        let mut counts = HashMap::new();
        for item in 0..1000 {
            let point = points.calc_candidates(&item).nth(0).unwrap();
            *counts.entry(point.to_string()).or_insert(0) += 1;
        }
        assert_eq!(counts["foo"], 246);
        assert_eq!(counts["bar"], 266);
        assert_eq!(counts["baz"], 237);
        assert_eq!(counts["qux"], 251);
    }

    #[test]
    fn weighted_points() {
        let mut points = NonUniformRendezvousPoints::default();
        points.insert("foo", Capacity::new(70).unwrap());
        points.insert("bar", Capacity::new(20).unwrap());
        points.insert("baz", Capacity::new(9).unwrap());
        points.insert("qux", Capacity::new(1).unwrap());

        let mut counts = HashMap::new();
        for item in 0..10000 {
            let point = points.calc_candidates(&item).nth(0).unwrap();
            *counts.entry(point.0.to_string()).or_insert(0) += 1;
        }
        assert_eq!(((counts["foo"] as f64) / 100.0).round(), 70.0);
        assert_eq!(((counts["bar"] as f64) / 100.0).round(), 20.0);
        assert_eq!(((counts["baz"] as f64) / 100.0).round(), 9.0);
        assert_eq!(((counts["qux"] as f64) / 100.0).round(), 1.0);
    }
}
