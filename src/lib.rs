#![allow(unused)]

//! Unsafe code in this module has been written keeping in mind two reasons:
//!
//!  1. Indexing with numbers that are guaranteed to be in-bounds does not
//!     not require bounds checking. Hence the `unsafe` counterparts of that
//!     can be used.
//!  2. Calling methods on `MaybeUninit` that assume that it is initialized is
//!     `unsafe` and we have used those methhods in the implementation only in
//!     those cases where the underlying `metadata` for that slot assures that
//!     the slot is `OCCUPIED`. In other cases, we refrain from calling those
//!     methods.

use std::borrow::Borrow;
use std::hash::{BuildHasher, Hash, RandomState};
use std::mem::MaybeUninit;
use std::vec::IntoIter;

pub struct HashTable<K, V, S> {
    pairs: Box<[MaybeUninit<(K, V)>]>,
    metadata: Box<[u8]>,
    hasher: S,
    capacity: usize,
    length: usize,
}

impl<K, V, S> Drop for HashTable<K, V, S> {
    fn drop(&mut self) {
        for (index, &element) in self.metadata.iter().enumerate() {
            if element == OCCUPIED {
                unsafe {
                    self.pairs.get_unchecked_mut(index).assume_init_drop();
                }
            }
        }
    }
}

impl<K, V> Default for HashTable<K, V, RandomState> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> HashTable<K, V, RandomState> {
    pub fn new() -> Self {
        Self {
            pairs: Vec::new().into_boxed_slice(),
            metadata: Vec::new().into_boxed_slice(),
            hasher: RandomState::new(),
            capacity: 0,
            length: 0,
        }
    }
}

const EMPTY: u8 = 0x00;
const TOMBSTONED: u8 = 0x01;
const OCCUPIED: u8 = 0x10;

impl<K, V, S> HashTable<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    pub fn with_hasher(s: S) -> Self {
        Self {
            pairs: Vec::new().into_boxed_slice(),
            metadata: Vec::new().into_boxed_slice(),
            hasher: s,
            capacity: 0,
            length: 0,
        }
    }

    #[inline]
    fn hash<M>(&self, key: &M) -> usize
    where
        M: Hash,
    {
        self.hasher.hash_one(key) as usize & (self.capacity - 1)
    }

    fn resize(&mut self) {
        let new_capacity = if self.capacity > 0 {
            2 * self.capacity
        } else {
            8
        };
        self.capacity = new_capacity;

        self.length = 0;

        // let mut old_vec = (0..new_capacity)
        //     .map(|_| MaybeUninit::uninit())
        //     .collect::<Vec<_>>()
        //     .into_boxed_slice();

        let mut old_vector = Vec::with_capacity(new_capacity);
        unsafe {
            old_vector.set_len(new_capacity);
        }
        let mut old_vec = old_vector.into_boxed_slice();

        let mut old_metadata = vec![EMPTY; new_capacity].into_boxed_slice();

        std::mem::swap(&mut old_vec, &mut self.pairs);
        std::mem::swap(&mut old_metadata, &mut self.metadata);

        let mut old_meta = old_metadata.into_iter();

        for (index, element) in old_vec.into_iter().enumerate() {
            let next_meta = old_meta
                .next()
                .expect("Metadata and pairs have the same length");
            if next_meta == OCCUPIED {
                let inner = unsafe { element.assume_init() };
                self.insert(inner.0, inner.1);
            }
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.length >= 3 * self.capacity / 4 {
            self.resize();
        }

        let mut hash = self.hash(&key);

        let mut current = unsafe { *self.metadata.get_unchecked(hash) };

        // Since the capacity is greater than length, it is guaranteed that the iteration is going
        // to find an empty slot before it reaches back to the original hash % capacity.
        loop {
            if current == EMPTY || current == TOMBSTONED {
                unsafe {
                    self.pairs.get_unchecked_mut(hash).write((key, value));
                    *self.metadata.get_unchecked_mut(hash) = OCCUPIED;
                }
                self.length += 1;
                return None;
            } else {
                let inner = unsafe { self.pairs.get_unchecked_mut(hash).assume_init_mut() };
                if inner.0 == key {
                    let mut old = value;
                    std::mem::swap(&mut inner.1, &mut old);
                    return Some(old);
                }
                hash = (hash + 1) & (self.capacity - 1);
                current = unsafe { *self.metadata.get_unchecked(hash) };
            }
        }
        None
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hash = self.hash(&key);
        let mut current = unsafe { *self.metadata.get_unchecked(hash) };

        let pivot = hash;

        loop {
            if current == EMPTY {
                return None;
            } else if current == OCCUPIED {
                let inner = unsafe { self.pairs.get_unchecked(hash).assume_init_ref() };
                if inner.0.borrow() == key {
                    return Some(&inner.1);
                }
            }
            hash = (hash + 1) & (self.capacity - 1);
            current = unsafe { *self.metadata.get_unchecked(hash) };
            if hash == pivot {
                return None;
            }
        }
        None
    }

    pub fn delete<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hash = self.hash(&key);
        let mut current = unsafe { *self.metadata.get_unchecked(hash) };

        let pivot = hash;

        loop {
            if current == EMPTY {
                return None;
            } else if current == OCCUPIED {
                let inner = unsafe { self.pairs.get_unchecked(hash).assume_init_ref() };
                if inner.0.borrow() == key {
                    let mut old = MaybeUninit::uninit();
                    std::mem::swap(unsafe { self.pairs.get_unchecked_mut(hash) }, &mut old);
                    let data = unsafe { old.assume_init() };

                    let next = (hash + 1) & (self.capacity - 1);
                    unsafe {
                        if *self.metadata.get_unchecked(next) == EMPTY {
                            *self.metadata.get_unchecked_mut(hash) = EMPTY;
                        } else {
                            *self.metadata.get_unchecked_mut(hash) = TOMBSTONED;
                        }
                    }

                    self.length -= 1;

                    return Some(data.1);
                }
            }
            hash = (hash + 1) & (self.capacity - 1);
            current = unsafe { *self.metadata.get_unchecked(hash) };
            if hash == pivot {
                return None;
            }
        }
        None
    }

    pub fn iter(&self) -> Iter<'_, K, V, S> {
        Iter {
            table: self,
            status: 0,
        }
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn length(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }
}

impl<K, V, S> IntoIterator for HashTable<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoTable<K, V>;

    fn into_iter(mut self) -> Self::IntoIter {
        let mut pairs = Vec::new().into_boxed_slice();
        let mut metadata = Vec::new().into_boxed_slice();
        std::mem::swap(&mut self.pairs, &mut pairs);
        std::mem::swap(&mut self.metadata, &mut metadata);
        IntoTable {
            pairs: pairs.into_iter(),
            metadata: metadata.into_iter(),
        }
    }
}

impl<'a, K, V, S> IntoIterator for &'a HashTable<K, V, S> {
    type Item = &'a (K, V);
    type IntoIter = Iter<'a, K, V, S>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            table: self,
            status: 0,
        }
    }
}

//impl<'a, K, V, S> IntoIterator for &'a mut HashTable<K, V, S> {
//    type Item = &'a mut (K, V);
//    type IntoIter = IterMut<'a, K, V, S>;
//
//    fn into_iter(self) -> Self::IntoIter {
//        IterMut {
//            table: self,
//            status: 0,
//        }
//    }
//}

pub struct IntoTable<K, V> {
    pairs: IntoIter<MaybeUninit<(K, V)>>,
    metadata: IntoIter<u8>,
}

impl<K, V> Iterator for IntoTable<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next_meta = self.metadata.next()?;
            let next_pair = self
                .pairs
                .next()
                .expect("Length of metadata and pairs is always equal!");

            if next_meta == OCCUPIED {
                let inner = unsafe { next_pair.assume_init() };
                break Some(inner);
            }
        }
    }
}

//pub struct IterMut<'a, K, V, S> {
//    table: &'a mut HashTable<K, V, S>,
//    status: usize,
//}
//
// Streaming Iterator Problem, Mutable references are not Copy so a reborrow happens and the
// returned thing does not live for 'a but for the lifetime of the &mut self and hence is rejected
// by the compiler
//impl<'a, K, V, S> Iterator for IterMut<'a, K, V, S> {
//    type Item = &'a mut (K, V);
//
//    fn next(&mut self) -> Option<Self::Item> {
//        loop {
//            if let Some(meta) = self.table.metadata.get(self.status) {
//                if *meta == OCCUPIED {
//                    let element = self
//                        .table
//                        .pairs
//                        .get_mut(self.status)
//                        .expect("Metadata and pairs have equal length");
//                    let element = unsafe { element.assume_init_mut() };
//                    break Some(element);
//                }
//                self.status += 1;
//            } else {
//                break None;
//            }
//        }
//    }
//}

// Not zero-cost in the truest sense!
// Streaming Iterator Problem does not occur here because shared references are copy and hence we
// do not need to reborrow and can return a reference with 'a and hence the code is accepted by the
// compiler.
pub struct Iter<'a, K, V, S> {
    table: &'a HashTable<K, V, S>,
    status: usize,
}

impl<'a, K, V, S> Iterator for Iter<'a, K, V, S> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(meta) = self.table.metadata.get(self.status) {
                if *meta == OCCUPIED {
                    // SAFETY: Metedata and pairs have equal length!
                    let element = unsafe { self.table.pairs.get_unchecked(self.status) };
                    let element = unsafe { element.assume_init_ref() };
                    break Some(element);
                }
                self.status += 1;
            } else {
                break None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut map = HashTable::new();

        let s = String::from("Abhinav");
        let sport = String::from("Football");

        map.insert(s, sport);

        assert!(!map.is_empty());

        assert_eq!(map.length(), 1);
        assert_eq!(map.capacity(), 8);

        let sport = String::from("Football");
        assert_eq!(map.get("Abhinav"), Some(&sport));

        assert_eq!(map.delete("Abhinav"), Some(String::from("Football")));
    }

    #[test]
    fn iterator() {
        let mut map = HashTable::new();
        map.insert(1, 2);
        map.insert(2, 4);
        map.insert(3, 6);
        map.insert(4, 8);

        let mut elements = map.into_iter().collect::<Vec<_>>();

        assert!(elements.pop().is_some());
        assert!(elements.pop().is_some());
        assert!(elements.pop().is_some());
        assert!(elements.pop().is_some());
        assert!(elements.pop().is_none());
    }

    use rand::Rng;
    use std::time::Instant;

    #[test]
    fn measure() {
        let mut map = HashTable::new();

        let mut rng = rand::rng();

        let keys = (0..1000).map(|_| rng.random::<u32>()).collect::<Vec<_>>();
        let cloned = keys.clone();

        let time = Instant::now();

        for (index, key) in keys.into_iter().enumerate() {
            map.insert(key, index);
        }

        for element in cloned.iter() {
            map.delete(element);
        }

        let time_taken = time.elapsed();

        println!("{:?}", time_taken.as_micros());

        assert!(map.is_empty());
    }
}
