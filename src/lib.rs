use std::hash::{DefaultHasher, Hash, Hasher};

const INITIAL_BUCKET_SIZE: usize = 1;

pub struct HashMap<K, V> {
    buckets: Vec<Vec<(K, V)>>,
    items: usize,
}

impl<K, V> HashMap<K, V> {
    pub fn new() -> Self {
        HashMap {
            buckets: Vec::new(),
            items: 0,
        }
    }
}

impl<K, V> HashMap<K, V>
where
    K: Hash + Eq,
{
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.buckets.is_empty() || self.items > 3 * self.buckets.len() / 4 {
            self.resize();
        }

        let mut new = DefaultHasher::new();
        key.hash(&mut new);
        let bucket: usize = (new.finish() % self.buckets.len() as u64) as usize;
        let target_bucket = &mut self.buckets[bucket];
        self.items += 1;
        for &mut (ref ekey, ref mut evalue) in target_bucket.iter_mut() {
            if ekey == &key {
                use std::mem;
                return Some(mem::replace(evalue, value));
            }
        }
        target_bucket.push((key, value));
        return None;
    }

    #[allow(unused_must_use)]
    pub fn resize(&mut self) {
        let target_size = match self.buckets.len() {
            0 => INITIAL_BUCKET_SIZE,
            n => 2 * n,
        };
        let mut new_vec = Vec::with_capacity(target_size);
        new_vec.extend((0..target_size).map(|_| Vec::new()));
        for (key, value) in self.buckets.iter_mut().flat_map(|bucket| bucket.drain(..)) {
            let mut hasher = DefaultHasher::new();
            key.hash(&mut hasher);
            let bucket = (hasher.finish() % new_vec.len() as u64) as usize;
            new_vec[bucket].push((key, value));
        }
        std::mem::replace(&mut self.buckets, new_vec);
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let bucket: usize = (hasher.finish() % self.buckets.len() as u64) as usize;
        self.buckets[bucket]
            .iter()
            .find(|&&(ref ekey, _)| ekey == &key)
            .map(|&(_, ref evalue)| evalue)
    }

    pub fn remove(&mut self, key: K) -> Option<(K, V)> {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let bucket = (hasher.finish() % self.buckets.len() as u64) as usize;
        let bucket = &mut self.buckets[bucket];
        let index = bucket.iter().position(|&(ref ekey, _)| ekey == &key)?;
        self.items -= 1;
        Some(bucket.swap_remove(index))
    }

    pub fn contains_key(&self, key: K) -> bool {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let bucket = (hasher.finish() % self.buckets.len() as u64) as usize;
        self.buckets[bucket]
            .iter()
            .find(|&&(ref ekey, _)| ekey == &key)
            .is_some()
    }

    pub fn size(&self) -> usize {
        self.items
    }

    pub fn is_empty(&self) -> bool {
        self.items == 0
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    map: &'a HashMap<K, V>,
    bucket: usize,
    at: usize,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.map.buckets.get(self.bucket) {
                Some(bucket) => match bucket.get(self.at) {
                    Some(&(ref ekey, ref evalue)) => {
                        self.at += 1;
                        break Some((ekey, evalue));
                    }
                    None => {
                        self.bucket += 1;
                        self.at = 0;
                        continue;
                    }
                },
                None => break None,
            }
        }
    }
}

impl<'a, K, V> IntoIterator for &'a HashMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            map: self,
            bucket: 0,
            at: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn insert() {
        let mut map = HashMap::new();
        map.insert("foo", 67);
        let get = map.get("foo");
        assert_eq!(get, Some(&67));
        assert_eq!(map.remove("foo"), Some(("foo", 67)));
        assert_eq!(map.get("foo"), None);
        assert_eq!(map.size(), 0);
    }

    #[test]
    fn iter() {
        let mut new = HashMap::new();
        new.insert("Abhinav", "Subhi");
        new.insert("Subhi", "Cat");
        new.insert("Abhinav2", "Rustacean");
        for ((&key, &value)) in new.into_iter() {
            match key {
                "Abhinav" => assert_eq!(value, "Subhi"),
                "Subhi" => assert_eq!(value, "Cat"),
                "Abhinav2" => assert_eq!(value, "Rustacean"),
                _ => unreachable!(),
            }
            assert_eq!(new.size(), 3);
        }
    }
}
