#![forbid(unsafe_code)]
// Copyright (c) 2016 btree multimap developers
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! A BTreeMultiMap implementation which is just a wrapper around std::collections::BTreeMap.
//! See BTreeMap's documentation for more details.
//!
//! Some of the methods are just thin wrappers, some methods does change a little semantics
//! and some methods are new (doesn't have an equivalent in BTreeMap.)
//!
//! The BTreeMultiMap is generic for the key (K) and the value (V). Internally the values are
//! stored in a generic Vector.
//!
//! # Examples
//!
//! ```
//! use btreemultimap::BTreeMultiMap;
//!
//! // create a new BTreeMultiMap. An explicit type signature can be omitted because of the
//! // type inference.
//! let mut queries = BTreeMultiMap::new();
//!
//! // insert some queries.
//! queries.insert("urls", "http://rust-lang.org");
//! queries.insert("urls", "http://mozilla.org");
//! queries.insert("urls", "http://wikipedia.org");
//! queries.insert("id", "42");
//! queries.insert("name", "roger");
//!
//! // check if there's any urls.
//! println!("Are there any urls in the btree multimap? {:?}.",
//!     if queries.contains_key("urls") {"Yes"} else {"No"} );
//!
//! // get the first item in a key's vector.
//! assert_eq!(queries.get("urls"), Some(&"http://rust-lang.org"));
//!
//! // get all the urls.
//! assert_eq!(queries.get_vec("urls"),
//!     Some(&vec!["http://rust-lang.org", "http://mozilla.org", "http://wikipedia.org"]));
//!
//! // iterate over all keys and the first value in the key's vector.
//! for (key, value) in queries.iter() {
//!     println!("key: {:?}, val: {:?}", key, value);
//! }
//!
//! // iterate over all keys and the key's vector.
//! for (key, values) in queries.iter() {
//!     println!("key: {:?}, values: {:?}", key, values);
//! }
//!
//! // the different methods for getting value(s) from the btree multimap.
//! let mut map = BTreeMultiMap::new();
//!
//! map.insert("key1", 42);
//! map.insert("key1", 1337);
//!
//! assert_eq!(map["key1"], 42);
//! assert_eq!(map.get("key1"), Some(&42));
//! assert_eq!(map.get_vec("key1"), Some(&vec![42, 1337]));
//! ```

use std::borrow::Borrow;
use std::collections::btree_map::{IntoIter, Keys};
use std::collections::btree_map::{Range, RangeMut};
use std::collections::BTreeMap;
use std::fmt::{self, Debug};
use std::iter::{FromIterator, IntoIterator, Iterator};
use std::ops::{Index, RangeBounds};

pub use entry::{Entry, OccupiedEntry, VacantEntry};

mod entry;

#[cfg(feature = "serde_impl")]
pub mod serde;

#[derive(Clone)]
pub struct BTreeMultiMap<K, V> {
    inner: BTreeMap<K, Vec<V>>,
}

impl<K, V> BTreeMultiMap<K, V>
where
    K: Ord,
{
    /// Creates an empty BTreeMultiMap
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map: BTreeMultiMap<&str, isize> = BTreeMultiMap::new();
    /// ```
    pub fn new() -> BTreeMultiMap<K, V> {
        BTreeMultiMap {
            inner: BTreeMap::new(),
        }
    }
}

impl<K, V> BTreeMultiMap<K, V>
where
    K: Ord,
{
    /// Inserts a key-value pair into the btreemultimap. If the key does exist in
    /// the map then the value is pushed to that key's vector. If the key doesn't
    /// exist in the map a new vector with the given value is inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert("key", 42);
    /// ```
    pub fn insert(&mut self, k: K, v: V) {
        match self.entry(k) {
            Entry::Occupied(mut entry) => {
                entry.get_vec_mut().push(v);
            }
            Entry::Vacant(entry) => {
                entry.insert_vec(vec![v]);
            }
        }
    }

    /// Inserts multiple key-value pairs into the btree multimap. If the key does exist in
    /// the map then the values are extended into that key's vector. If the key
    /// doesn't exist in the map a new vector collected from the given values is inserted.
    ///
    /// This may be more efficient than inserting values independently.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<&str, &usize>::new();
    /// map.insert_many("key", &[42, 43]);
    /// ```
    pub fn insert_many<I: IntoIterator<Item = V>>(&mut self, k: K, v: I) {
        match self.entry(k) {
            Entry::Occupied(mut entry) => {
                entry.get_vec_mut().extend(v);
            }
            Entry::Vacant(entry) => {
                entry.insert_vec(v.into_iter().collect::<Vec<_>>());
            }
        }
    }

    /// Inserts multiple key-value pairs into the btree multimap. If the key does exist in
    /// the map then the values are extended into that key's vector. If the key
    /// doesn't exist in the map a new vector collected from the given values is inserted.
    ///
    /// This may be more efficient than inserting values independently.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<&str, usize>::new();
    /// map.insert_many_from_slice("key", &[42, 43]);
    /// ```
    pub fn insert_many_from_slice(&mut self, k: K, v: &[V])
    where
        V: Clone,
    {
        match self.entry(k) {
            Entry::Occupied(mut entry) => {
                entry.get_vec_mut().extend_from_slice(v);
            }
            Entry::Vacant(entry) => {
                entry.insert_vec(v.to_vec());
            }
        }
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.contains_key(k)
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 52);
    /// map.insert(2, 1337);
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.iter().len()
    }

    /// Removes a key from the map, returning the vector of values at
    /// the key if the key was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// assert_eq!(map.remove(&1), Some(vec![42, 1337]));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<Vec<V>>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.remove(k)
    }

    /// Returns a reference to the first item in the vector corresponding to
    /// the key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// assert_eq!(map.get(&1), Some(&42));
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.get(k).and_then(|a| a.iter().next())
    }

    /// Returns a mutable reference to the first item in the vector corresponding to
    /// the key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// if let Some(v) = map.get_mut(&1) {
    ///     *v = 99;
    /// }
    /// assert_eq!(map[&1], 99);
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.get_mut(k).and_then(|a| a.iter_mut().next())
    }

    /// Returns a reference to the vector corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// assert_eq!(map.get_vec(&1), Some(&vec![42, 1337]));
    /// ```
    pub fn get_vec<Q: ?Sized>(&self, k: &Q) -> Option<&Vec<V>>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.get(k)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_values(&1), Some((&1, &vec!["a"])));
    /// assert_eq!(map.get_key_values(&2), None);
    /// ```
    pub fn get_key_values<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &Vec<V>)>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.get_key_value(k)
    }

    /// Returns a mutable reference to the vector corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// if let Some(v) = map.get_vec_mut(&1) {
    ///     (*v)[0] = 1991;
    ///     (*v)[1] = 2332;
    /// }
    /// assert_eq!(map.get_vec(&1), Some(&vec![1991, 2332]));
    /// ```
    pub fn get_vec_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut Vec<V>>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.inner.get_mut(k)
    }

    /// Returns true if the key is multi-valued.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1, 42);
    /// map.insert(1, 1337);
    /// map.insert(2, 2332);
    ///
    /// assert_eq!(map.is_vec(&1), true);   // key is multi-valued
    /// assert_eq!(map.is_vec(&2), false);  // key is single-valued
    /// assert_eq!(map.is_vec(&3), false);  // key not in map
    /// ```
    pub fn is_vec<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        match self.get_vec(k) {
            Some(val) => val.len() > 1,
            None => false,
        }
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1,42);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Clears the map, removing all key-value pairs.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1,42);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// An iterator visiting all keys in arbitrary order.
    /// Iterator element type is &'a K.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1,42);
    /// map.insert(2,1337);
    /// map.insert(4,1991);
    ///
    /// for key in map.keys() {
    ///     println!("{:?}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, Vec<V>> {
        self.inner.keys()
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator returns
    /// a reference to the key and the first element in the corresponding key's vector.
    /// Iterator element type is (&'a K, &'a V).
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1,42);
    /// map.insert(1,1337);
    /// map.insert(3,2332);
    /// map.insert(4,1991);
    ///
    /// for (key, value) in map.iter() {
    ///     println!("key: {:?}, val: {:?}", key, value);
    /// }
    /// ```
    pub fn iter(&self) -> MultiIter<K, V> {
        MultiIter {
            vec: None,
            inner: self.inner.iter(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator returns
    /// a reference to the key and a mutable reference to the first element in the
    /// corresponding key's vector. Iterator element type is (&'a K, &'a mut V).
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(1,42);
    /// map.insert(1,1337);
    /// map.insert(3,2332);
    /// map.insert(4,1991);
    ///
    /// for (_, value) in map.iter_mut() {
    ///     *value *= *value;
    /// }
    ///
    /// for (key, value) in map.iter() {
    ///     println!("key: {:?}, val: {:?}", key, value);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> MultiIterMut<K, V> {
        MultiIterMut {
            vec: None,
            inner: self.inner.iter_mut(),
        }
    }

    /// Gets the specified key's corresponding entry in the map for in-place manipulation.
    /// It's possible to both manipulate the vector and the 'value' (the first value in the
    /// vector).
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut m = BTreeMultiMap::new();
    /// m.insert(1, 42);
    ///
    /// {
    ///     let mut v = m.entry(1).or_insert(43);
    ///     assert_eq!(v, &42);
    ///     *v = 44;
    /// }
    /// assert_eq!(m.entry(2).or_insert(666), &666);
    ///
    /// {
    ///     let mut v = m.entry(1).or_insert_vec(vec![43]);
    ///     assert_eq!(v, &vec![44]);
    ///     v.push(50);
    /// }
    /// assert_eq!(m.entry(2).or_insert_vec(vec![666]), &vec![666]);
    ///
    /// assert_eq!(m.get_vec(&1), Some(&vec![44, 50]));
    /// ```
    pub fn entry(&mut self, k: K) -> Entry<K, V> {
        use std::collections::btree_map::Entry as BTreeMapEntry;
        match self.inner.entry(k) {
            BTreeMapEntry::Occupied(entry) => Entry::Occupied(OccupiedEntry { inner: entry }),
            BTreeMapEntry::Vacant(entry) => Entry::Vacant(VacantEntry { inner: entry }),
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(&k,&mut v)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut m = BTreeMultiMap::new();
    /// m.insert(1, 42);
    /// m.insert(1, 99);
    /// m.insert(2, 42);
    /// m.retain(|&k, &v| { k == 1 && v == 42 });
    /// assert_eq!(1, m.len());
    /// assert_eq!(Some(&42), m.get(&1));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &V) -> bool,
    {
        self.inner.retain(|key, vector| {
            vector.retain(|value| f(key, value));
            !vector.is_empty()
        });
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = BTreeMultiMap::new();
    /// map.insert(3, "a");
    /// map.insert(5, "b");
    /// map.insert(5, "c");
    /// map.insert(8, "c");
    /// map.insert(9, "d");
    /// for (&key, &value) in map.range((Included(&4), Included(&8))) {
    ///     println!("{}: {}", key, value);
    /// }
    /// let mut iter = map.range(4..=8);
    /// assert_eq!(Some((&5, &"b")), iter.next());
    /// assert_eq!(Some((&5, &"c")), iter.next());
    /// assert_eq!(Some((&8, &"c")), iter.next());
    /// assert_eq!(None, iter.next());
    /// ```
    pub fn range<T: ?Sized, R>(&self, range: R) -> MultiRange<'_, K, V>
    where
        T: Ord,
        K: Borrow<T>,
        R: RangeBounds<T>,
    {
        MultiRange {
            vec: None,
            inner: self.inner.range(range),
        }
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements in the map.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btreemultimap::BTreeMultiMap;
    ///
    /// let mut map: BTreeMultiMap<&str, i32> = ["Alice", "Bob", "Carol", "Cheryl"]
    ///     .iter()
    ///     .map(|&s| (s, 0))
    ///     .collect();
    /// for (_, balance) in map.range_mut("B".."Cheryl") {
    ///     *balance += 100;
    /// }
    /// for (name, balance) in &map {
    ///     println!("{} => {}", name, balance);
    /// }
    /// ```
    pub fn range_mut<T: ?Sized, R>(&mut self, range: R) -> MultiRangeMut<'_, K, V>
    where
        T: Ord,
        K: Borrow<T>,
        R: RangeBounds<T>,
    {
        MultiRangeMut {
            vec: None,
            inner: self.inner.range_mut(range),
        }
    }
}

pub struct MultiRange<'a, K, V> {
    vec: Option<(&'a K, std::slice::Iter<'a, V>)>,
    inner: Range<'a, K, Vec<V>>,
}

impl<'a, K, V> Clone for MultiRange<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
            inner: self.inner.clone(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for MultiRange<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K, V> Iterator for MultiRange<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }

    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for MultiRange<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next_back() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next_back() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }
}

pub struct MultiRangeMut<'a, K, V> {
    vec: Option<(&'a K, std::slice::IterMut<'a, V>)>,
    inner: RangeMut<'a, K, Vec<V>>,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for MultiRangeMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K, V> Iterator for MultiRangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter_mut()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }

    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for MultiRangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next_back() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next_back() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter_mut()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }
}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for BTreeMultiMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    type Output = V;

    fn index(&self, index: &Q) -> &V {
        self.inner
            .get(index)
            .map(|v| &v[0])
            .expect("no entry found for key")
    }
}

impl<K, V> Debug for BTreeMultiMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> PartialEq for BTreeMultiMap<K, V>
where
    K: Ord,
    V: PartialEq,
{
    fn eq(&self, other: &BTreeMultiMap<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .zip(other.iter())
            .all(|(a, b)| a.0 == b.0 && a.1 == b.1)
    }
}

impl<K, V> Eq for BTreeMultiMap<K, V>
where
    K: Ord,
    V: Eq,
{
}

impl<K, V> Default for BTreeMultiMap<K, V>
where
    K: Ord,
{
    fn default() -> BTreeMultiMap<K, V> {
        BTreeMultiMap {
            inner: Default::default(),
        }
    }
}

impl<K, V> FromIterator<(K, V)> for BTreeMultiMap<K, V>
where
    K: Ord,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iterable: T) -> BTreeMultiMap<K, V> {
        let iter = iterable.into_iter();

        let mut multimap = BTreeMultiMap::new();
        for (k, v) in iter {
            multimap.insert(k, v);
        }

        multimap
    }
}

impl<'a, K, V> IntoIterator for &'a BTreeMultiMap<K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);
    type IntoIter = MultiIter<'a, K, V>;

    fn into_iter(self) -> MultiIter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut BTreeMultiMap<K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = MultiIterMut<'a, K, V>;

    fn into_iter(self) -> MultiIterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V> IntoIterator for BTreeMultiMap<K, V>
where
    K: Ord,
{
    type Item = (K, Vec<V>);
    type IntoIter = IntoIter<K, Vec<V>>;

    fn into_iter(self) -> IntoIter<K, Vec<V>> {
        self.inner.into_iter()
    }
}

impl<K, V> Extend<(K, V)> for BTreeMultiMap<K, V>
where
    K: Ord,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for BTreeMultiMap<K, V>
where
    K: Ord + Copy,
    V: Copy,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
    }
}

impl<K, V> Extend<(K, Vec<V>)> for BTreeMultiMap<K, V>
where
    K: Ord,
{
    fn extend<T: IntoIterator<Item = (K, Vec<V>)>>(&mut self, iter: T) {
        for (k, values) in iter {
            match self.entry(k) {
                Entry::Occupied(mut entry) => {
                    entry.get_vec_mut().extend(values);
                }
                Entry::Vacant(entry) => {
                    entry.insert_vec(values);
                }
            }
        }
    }
}

impl<'a, K, V> Extend<(&'a K, &'a Vec<V>)> for BTreeMultiMap<K, V>
where
    K: Ord + Copy,
    V: Copy,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a Vec<V>)>>(&mut self, iter: T) {
        self.extend(
            iter.into_iter()
                .map(|(&key, values)| (key, values.to_owned())),
        );
    }
}

pub struct MultiIter<'a, K, V> {
    vec: Option<(&'a K, std::slice::Iter<'a, V>)>,
    inner: std::collections::btree_map::Iter<'a, K, Vec<V>>,
}

impl<'a, K, V> Clone for MultiIter<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for MultiIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a V)> {
        self.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for MultiIter<'a, K, V> {
    fn len(&self) -> usize {
        let mut ret: usize = 0;
        for pair in self.inner.clone() {
            ret += pair.1.len();
        }
        ret
    }
}

impl<'a, K, V> DoubleEndedIterator for MultiIter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next_back() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next_back() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }
}

pub struct MultiIterMut<'a, K, V> {
    vec: Option<(&'a K, std::slice::IterMut<'a, V>)>,
    inner: std::collections::btree_map::IterMut<'a, K, Vec<V>>,
}

impl<'a, K, V> Iterator for MultiIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter_mut()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn last(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }

    fn min(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next()
    }

    fn max(mut self) -> Option<(&'a K, &'a mut V)> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for MultiIterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if let Some(a) = self.vec.as_mut() {
                if let Some(ret) = a.1.next_back() {
                    return Some((a.0, ret));
                }
            }
            match self.inner.next_back() {
                Some((a, b)) => {
                    self.vec = Some((a, b.iter_mut()));
                    continue;
                }
                None => {
                    return None;
                }
            }
        }
    }
}

#[macro_export]
/// Create a `BTreeMultiMap` from a list of key value pairs
///
/// ## Example
///
/// ```
/// # use btreemultimap::BTreeMultiMap;
/// #[macro_use] extern crate btreemultimap;
/// # fn main(){
///
/// let map = btreemultimap!(
///     "dog" => "husky",
///     "dog" => "retreaver",
///     "dog" => "shiba inu",
///     "cat" => "cat"
///     );
/// # }
///
/// ```
macro_rules! btreemultimap{
    (@replace_with_unit $_t:tt) => { () };
    (@count $($key:expr),*) => { <[()]>::len(&[$($crate::btreemultimap! { @replace_with_unit $key }),*]) };

    ($($key:expr => $value:expr),* $(,)?)=>{
        {
            let mut map = $crate::BTreeMultiMap::new();
            $(
                map.insert($key,$value);
             )*
            map
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::iter::FromIterator;

    use super::*;

    #[test]
    fn create() {
        let _: BTreeMultiMap<usize, usize> = BTreeMultiMap {
            inner: BTreeMap::new(),
        };
    }

    #[test]
    fn new() {
        let _: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
    }

    #[test]
    fn insert() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 3);
    }

    #[test]
    fn insert_many() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert_many(1, vec![3, 4]);
        assert_eq!(Some(&vec![3, 4]), m.get_vec(&1));
    }

    #[test]
    fn insert_many_again() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 2);
        m.insert_many(1, vec![3, 4]);
        assert_eq!(Some(&vec![2, 3, 4]), m.get_vec(&1));
    }

    #[test]
    fn insert_many_from_slice() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert_many_from_slice(1, &[3, 4]);
        assert_eq!(Some(&vec![3, 4]), m.get_vec(&1));
    }

    #[test]
    fn insert_many_from_slice_again() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 2);
        m.insert_many_from_slice(1, &[3, 4]);
        assert_eq!(Some(&vec![2, 3, 4]), m.get_vec(&1));
    }

    #[test]
    fn insert_existing() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 3);
        m.insert(1, 4);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn index_no_entry() {
        let m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        &m[&1];
    }

    #[test]
    fn index() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        let values = m[&1];
        assert_eq!(values, 42);
    }

    #[test]
    fn contains_key_true() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        assert!(m.contains_key(&1));
    }

    #[test]
    fn contains_key_false() {
        let m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        assert_eq!(m.contains_key(&1), false);
    }

    #[test]
    fn len() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(2, 1337);
        m.insert(3, 99);
        assert_eq!(m.len(), 3);
    }

    #[test]
    fn remove_not_present() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        let v = m.remove(&1);
        assert_eq!(v, None);
    }

    #[test]
    fn remove_present() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        let v = m.remove(&1);
        assert_eq!(v, Some(vec![42]));
    }

    #[test]
    fn get_not_present() {
        let m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        assert_eq!(m.get(&1), None);
    }

    #[test]
    fn get_present() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        assert_eq!(m.get(&1), Some(&42));
    }

    #[test]
    fn get_vec_not_present() {
        let m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        assert_eq!(m.get_vec(&1), None);
    }

    #[test]
    fn get_vec_present() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 1337);
        assert_eq!(m.get_vec(&1), Some(&vec![42, 1337]));
    }

    #[test]
    fn is_empty_true() {
        let m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        assert_eq!(m.is_empty(), true);
    }

    #[test]
    fn is_empty_false() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        assert_eq!(m.is_empty(), false);
    }

    #[test]
    fn clear() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.clear();
        assert!(m.is_empty());
    }

    #[test]
    fn get_mut() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        if let Some(v) = m.get_mut(&1) {
            *v = 1337;
        }
        assert_eq!(m[&1], 1337)
    }

    #[test]
    fn get_vec_mut() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 1337);
        if let Some(v) = m.get_vec_mut(&1) {
            (*v)[0] = 5;
            (*v)[1] = 10;
        }
        assert_eq!(m.get_vec(&1), Some(&vec![5, 10]))
    }

    #[test]
    fn keys() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(2, 42);
        m.insert(4, 42);
        m.insert(8, 42);

        let keys: Vec<_> = m.keys().cloned().collect();
        assert_eq!(keys.len(), 4);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&4));
        assert!(keys.contains(&8));
    }

    #[test]
    fn iter() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 42);
        m.insert(4, 42);
        m.insert(8, 42);

        let mut iter = m.iter();

        for _ in iter.by_ref().take(2) {}

        assert_eq!(iter.len(), 2);
    }

    #[test]
    fn clone_iter_with_not_cloneable_items() {
        #[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
        struct Foo(usize);

        let mut m = BTreeMultiMap::new();
        m.insert(Foo(1), Foo(42));
        m.insert(Foo(1), Foo(42));
        m.insert(Foo(4), Foo(42));
        m.insert(Foo(8), Foo(42));

        let iter = m.iter();

        let mut iter_clone = iter.clone();
        for _ in iter_clone.by_ref().take(2) {}

        assert_eq!(iter.len(), 4);
        assert_eq!(iter_clone.len(), 2);
    }

    #[test]
    fn intoiterator_for_reference_type() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 43);
        m.insert(1, 44);
        m.insert(4, 42);
        m.insert(8, 42);

        let keys = vec![1, 4, 8];

        for (key, value) in &m {
            assert!(keys.contains(key));

            if key == &1 {
                assert!(value == &43 || value == &44);
            } else {
                assert_eq!(value, &42);
            }
        }
    }

    #[test]
    fn intoiterator_for_mutable_reference_type() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 43);
        m.insert(1, 44);
        m.insert(4, 42);
        m.insert(8, 42);

        let keys = vec![1, 4, 8];

        for (key, value) in &mut m {
            assert!(keys.contains(key));

            if key == &1 {
                assert!(value == &43 || value == &44);
                *value = 666;
            } else {
                assert_eq!(value, &42);
            }
        }

        assert_eq!(m.get_vec(&1), Some(&vec![666, 666]));
    }

    #[test]
    fn intoiterator_consuming() {
        let mut m: BTreeMultiMap<usize, usize> = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 43);
        m.insert(4, 42);
        m.insert(8, 42);

        let keys = vec![1, 4, 8];

        for (key, value) in m {
            assert!(keys.contains(&key));

            if key == 1 {
                assert_eq!(value, vec![42, 43]);
            } else {
                assert_eq!(value, vec![42]);
            }
        }
    }

    #[test]
    fn test_eq() {
        let mut m1 = BTreeMultiMap::new();
        m1.insert(1, 2);
        m1.insert(2, 3);
        m1.insert(3, 4);
        let mut m2 = BTreeMultiMap::new();
        m2.insert(1, 2);
        m2.insert(2, 3);
        assert!(m1 != m2);
        m2.insert(3, 4);
        assert_eq!(m1, m2);
        m2.insert(3, 4);
        assert!(m1 != m2);
        m1.insert(3, 4);
        assert_eq!(m1, m2);
    }

    #[test]
    fn test_default() {
        let _: BTreeMultiMap<u8, u8> = Default::default();
    }

    #[test]
    fn test_from_iterator() {
        let vals: Vec<(&str, i64)> = vec![("foo", 123), ("bar", 456), ("foo", 789)];
        let multimap: BTreeMultiMap<&str, i64> = BTreeMultiMap::from_iter(vals);

        let foo_vals: &Vec<i64> = multimap.get_vec("foo").unwrap();
        assert!(foo_vals.contains(&123));
        assert!(foo_vals.contains(&789));

        let bar_vals: &Vec<i64> = multimap.get_vec("bar").unwrap();
        assert!(bar_vals.contains(&456));
    }

    #[test]
    fn test_extend_consuming_btree_hashmap() {
        let mut a = BTreeMultiMap::new();
        a.insert(1, 42);

        let mut b = BTreeMap::new();
        b.insert(1, 43);
        b.insert(2, 666);

        a.extend(b);

        assert_eq!(a.len(), 3);
        assert_eq!(a.get_vec(&1), Some(&vec![42, 43]));
    }

    #[test]
    fn test_extend_ref_btreemap() {
        let mut a = BTreeMultiMap::new();
        a.insert(1, 42);

        let mut b = BTreeMap::new();
        b.insert(1, 43);
        b.insert(2, 666);

        a.extend(&b);

        assert_eq!(a.len(), 3);
        assert_eq!(a.get_vec(&1), Some(&vec![42, 43]));
        assert_eq!(b.len(), 2);
        assert_eq!(b[&1], 43);
    }

    #[test]
    fn test_extend_consuming_multimap() {
        let mut a = BTreeMultiMap::new();
        a.insert(1, 42);

        let mut b = BTreeMultiMap::new();
        b.insert(1, 43);
        b.insert(1, 44);
        b.insert(2, 666);

        a.extend(b);

        assert_eq!(a.len(), 4);
        assert_eq!(a.get_vec(&1), Some(&vec![42, 43, 44]));
    }

    #[test]
    fn test_extend_ref_multimap() {
        let mut a = BTreeMultiMap::new();
        a.insert(1, 42);

        let mut b = BTreeMultiMap::new();
        b.insert(1, 43);
        b.insert(1, 44);
        b.insert(2, 666);

        a.extend(&b);

        assert_eq!(a.len(), 4);
        assert_eq!(a.get_vec(&1), Some(&vec![42, 43, 44]));
        assert_eq!(b.len(), 3);
        assert_eq!(b.get_vec(&1), Some(&vec![43, 44]));
    }

    #[test]
    fn test_entry() {
        let mut m = BTreeMultiMap::new();
        m.insert(1, 42);

        {
            let v = m.entry(1).or_insert(43);
            assert_eq!(v, &42);
            *v = 44;
        }
        assert_eq!(m.entry(2).or_insert(666), &666);

        assert_eq!(m[&1], 44);
        assert_eq!(m[&2], 666);
    }

    #[test]
    fn test_entry_vec() {
        let mut m = BTreeMultiMap::new();
        m.insert(1, 42);

        {
            let v = m.entry(1).or_insert_vec(vec![43]);
            assert_eq!(v, &vec![42]);
            *v.first_mut().unwrap() = 44;
        }
        assert_eq!(m.entry(2).or_insert_vec(vec![666]), &vec![666]);

        assert_eq!(m[&1], 44);
        assert_eq!(m[&2], 666);
    }

    #[test]
    fn test_is_vec() {
        let mut m = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 1337);
        m.insert(2, 2332);

        assert!(m.is_vec(&1));
        assert!(!m.is_vec(&2));
        assert!(!m.is_vec(&3));
    }

    #[test]
    fn test_macro() {
        let mut manual_map = BTreeMultiMap::new();
        manual_map.insert("key1", 42);
        assert_eq!(manual_map, btreemultimap!("key1" => 42));

        manual_map.insert("key1", 1337);
        manual_map.insert("key2", 2332);
        let macro_map = btreemultimap! {
            "key1" =>    42,
            "key1" =>  1337,
            "key2" =>  2332
        };
        assert_eq!(manual_map, macro_map);
    }

    #[test]
    fn retain_removes_element() {
        let mut m = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 99);
        m.retain(|&k, &v| k == 1 && v == 42);
        assert_eq!(1, m.len());
        assert_eq!(Some(&42), m.get(&1));
    }

    #[test]
    fn retain_also_removes_empty_vector() {
        let mut m = BTreeMultiMap::new();
        m.insert(1, 42);
        m.insert(1, 99);
        m.insert(2, 42);
        m.retain(|&k, &v| k == 1 && v == 42);
        assert_eq!(1, m.len());
        assert_eq!(Some(&42), m.get(&1));
    }
}
