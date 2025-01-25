use ordermap::OrderMap;

pub(crate) type Map<V> = OrderMap<String, V>;

pub(crate) trait StringMapLike<V>: Default + IntoIterator {
    fn keys(&self) -> impl Iterator<Item = &str>;

    fn values<'a>(&'a self) -> impl Iterator<Item = &'a V>
    where
        V: 'a;

    fn get(&self, key: &str) -> Option<&V>;

    fn remove(&mut self, key: &str) -> Option<V>;

    fn insert(&mut self, key: String, value: V);

    fn len(&self) -> usize;

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a str, &'a V)>
    where
        V: 'a;

    fn union(first: Self, second: Self, merge: impl Fn(V, V) -> V) -> Self
    where
        Self: Default,
        V: Clone,
    {
        let mut result = Self::default();
        let all_keys = first.keys().chain(second.keys()).collect::<Vec<_>>();
        for key in all_keys.into_iter() {
            if result.get(key).is_none() {
                let value = match (first.get(key), second.get(key)) {
                    (None, Some(v)) => v.clone(),
                    (Some(v), None) => v.clone(),
                    (Some(v1), Some(v2)) => merge(v1.clone(), v2.clone()),
                    (None, None) => unreachable!(),
                };
                result.insert(key.to_owned(), value);
            }
        }
        result
    }
}

impl<V: std::hash::Hash + Eq> StringMapLike<V> for Map<V> {
    fn keys(&self) -> impl Iterator<Item = &str> {
        self.keys().map(String::as_str)
    }

    fn values<'a>(&'a self) -> impl Iterator<Item = &'a V>
    where
        V: 'a,
    {
        self.values()
    }

    fn get(&self, key: &str) -> Option<&V> {
        OrderMap::get(self, key)
    }

    fn remove(&mut self, key: &str) -> Option<V> {
        OrderMap::remove(self, key)
    }

    fn insert(&mut self, key: String, value: V) {
        OrderMap::insert(self, key, value);
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a str, &'a V)>
    where
        V: 'a,
    {
        self.iter().map(|(k, v)| (k.as_str(), v))
    }
}
