use std::vec;
use std::slice;

use node::Node;

pub fn iter<'a, T>(iter: slice::Iter<'a, Node<T>>) -> Iter<'a, T> {
    Iter(iter)
}

/// An iterator over the nodes of a candidate set.
pub struct Iter<'a, T: 'a>(slice::Iter<'a, Node<T>>);
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| &n.node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub fn into_iter<T>(iter: vec::IntoIter<Node<T>>) -> IntoIter<T> {
    IntoIter(iter)
}

/// An owning iterator over the nodes of a candidate set.
pub struct IntoIter<T>(vec::IntoIter<Node<T>>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| n.node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub fn candidates<'a, T: 'a>(inner: slice::Iter<'a, Node<T>>) -> Candidates<T> {
    Candidates(inner)
}

/// An iterator which represents a sequence of the candidate nodes for a rendezvous.
///
/// The higher priority node is placed in front of this sequence.
pub struct Candidates<'a, T: 'a>(slice::Iter<'a, Node<T>>);
impl<'a, T: 'a> Iterator for Candidates<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| &n.node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub mod heterogeneous {
    use std::vec;
    use std::slice;

    use Capacity;
    use node::WeightedNode;

    pub fn iter<'a, T>(iter: slice::Iter<'a, WeightedNode<T>>) -> Iter<'a, T> {
        Iter(iter)
    }

    /// An iterator over the nodes of a candidate set.
    pub struct Iter<'a, T: 'a>(slice::Iter<'a, WeightedNode<T>>);
    impl<'a, T: 'a> Iterator for Iter<'a, T> {
        type Item = (&'a T, Capacity);
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|n| (&n.node, n.capacity))
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }

    pub fn into_iter<T>(iter: vec::IntoIter<WeightedNode<T>>) -> IntoIter<T> {
        IntoIter(iter)
    }

    /// An owning iterator over the nodes of a candidate set.
    pub struct IntoIter<T>(vec::IntoIter<WeightedNode<T>>);
    impl<T> Iterator for IntoIter<T> {
        type Item = (T, Capacity);
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|n| n.into_tuple())
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }

    pub fn candidates<'a, T: 'a>(inner: slice::Iter<'a, WeightedNode<T>>) -> Candidates<T> {
        Candidates(inner)
    }

    /// An iterator which represents a sequence of the candidate nodes for a rendezvous.
    ///
    /// The higher priority node is placed in front of this sequence.
    pub struct Candidates<'a, T: 'a>(slice::Iter<'a, WeightedNode<T>>);
    impl<'a, T: 'a> Iterator for Candidates<'a, T> {
        type Item = (&'a T, Capacity);
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|n| (&n.node, n.capacity))
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }
}
