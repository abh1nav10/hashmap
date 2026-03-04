#[cfg(test)]
mod tests {
    use hashmap::HashTable;

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
