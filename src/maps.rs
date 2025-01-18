pub(crate) type Map<V> = std::collections::BTreeMap<String, V>;

pub(crate) trait StringMapLike<V>: Default + IntoIterator {
    fn keys(&self) -> impl Iterator<Item = &str>;

    fn values<'a>(&'a self) -> impl Iterator<Item = &'a V>
    where
        V: 'a;

    fn get(&self, key: &str) -> Option<&V>;

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
        let all_keys = first
            .keys()
            .chain(second.keys())
            .map(str::to_owned)
            .collect::<std::collections::BTreeSet<_>>();
        for key in all_keys.into_iter() {
            let value = match (first.get(&key), second.get(&key)) {
                (None, Some(v)) => v.clone(),
                (Some(v), None) => v.clone(),
                (Some(v1), Some(v2)) => merge(v1.clone(), v2.clone()),
                (None, None) => unreachable!(),
            };
            result.insert(key.to_owned(), value);
        }
        result
    }
}
impl<V> StringMapLike<V> for Map<V> {
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
        std::collections::BTreeMap::get(self, key)
    }

    fn insert(&mut self, key: String, value: V) {
        self.insert(key, value);
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
