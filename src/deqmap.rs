// deqmap::deqmap
//
//!
//

use crate::error::{Error, Result};
use core::{borrow::Borrow, cmp::min, hash::Hash};
use std::collections::{
    hash_map::{Entry, HashMap},
    VecDeque,
};

/// A double-ended, ordered collection of elements with optional keys,
/// leveraging a [`VecDeque`] and a [`HashMap`].
#[derive(Clone, Debug, Default)]
pub struct DeqMap<K: Hash + Eq, V> {
    vec: VecDeque<V>,
    map: HashMap<K, usize>,
}

/// # general construction & configuration
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns a new empty deqmap.
    pub fn new() -> DeqMap<K, V> {
        DeqMap {
            vec: VecDeque::default(),
            map: HashMap::default(),
        }
    }

    /// Returns a new deqmap filled from a vec of values.
    pub fn from_vec(values: Vec<V>) -> DeqMap<K, V> {
        let mut qm = Self::with_capacity(values.len(), 0);
        qm.extend(values);
        qm
    }

    /// Returns a new empty `DeqMap`, with at least the specified `total`
    /// capacity and `keyed` capacity.
    ///
    /// If either capacity is 0, it will not be allocated.
    ///
    /// # Panics
    /// Panics if either capacity exceeds [`isize::MAX`] bytes.
    pub fn with_capacity(total: usize, keyed: usize) -> DeqMap<K, V> {
        assert![total >= keyed];
        DeqMap {
            vec: VecDeque::with_capacity(total),
            map: HashMap::with_capacity(keyed),
        }
    }

    /// Returns the number of unkeyed elements the deqmap can hold without
    /// reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Returns the number of keyed elements the deqmap can hold without
    /// reallocating.
    #[inline]
    pub fn capacity_keyed(&self) -> usize {
        min(self.vec.capacity(), self.map.capacity())
    }

    /// Reserves capacity for at least `additional` more *total* elements
    /// to be inserted.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional);
    }
    // try_reserve_

    /// Reserves capacity for at least `additional` more **keyed** elements
    /// to be inserted.
    #[inline]
    pub fn reserve_keyed(&mut self, additional: usize) {
        self.vec.reserve(additional - self.vec.capacity());
        self.map.reserve(additional);
    }

    /// Shrinks the capacity of the deqmap as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit();
        self.map.shrink_to_fit();
    }

    /// Returns a slice of the values in order.
    pub fn as_slice(&mut self) -> &[V] {
        self.vec.make_contiguous();
        self.vec.as_slices().0
    }

    /// Returns a mutable slice of the values in order.
    pub fn as_mut_slice(&mut self) -> &[V] {
        self.vec.make_contiguous()
    }
}

/// # general query, retrieval, insertion & removal
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns the total number of elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns only the number of keyed elements.
    #[inline]
    pub fn len_keyed(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if there are no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Returns `true` if there are no *keyed* elements.
    #[inline]
    pub fn is_empty_keyed(&self) -> bool {
        self.vec.is_empty()
    }

    /// Clears the deqmap, removing all values.
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear();
        self.map.clear();
    }

    /// Provides a reference to the front element,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn front(&self) -> Option<&V> {
        self.vec.front()
    }

    /// Provides a mutable reference to the front element,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut V> {
        self.vec.front_mut()
    }

    /// Provides a reference to the back element,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn back(&self) -> Option<&V> {
        self.vec.back()
    }

    /// Provides a mutable reference to the back element,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut V> {
        self.vec.back_mut()
    }

    /// Removes the front element and returns it, or `None` if the deqmap is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<V> {
        // remove any keyed entry pointing to the first value.
        let idx = 0;
        self.map.retain(|_, v| *v != idx);

        self.vec.pop_front()
    }

    /// Removes the front element and returns it alongside its key, if any,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn pop_front_with_key(&mut self) -> Option<(Option<K>, V)>
    where
        K: Clone,
    {
        let idx = 0;
        let key = self.find_key_unchecked(idx).cloned();
        if let Some(ref k) = key {
            self.map.remove_entry(k);
        };
        self.vec.pop_front().map(|v| (key, v))
    }

    /// Removes the back element and returns it, or `None` if the deqmap is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<V> {
        // remove any keyed entry pointing to the last value.
        let idx = self.len() - 1;
        self.map.retain(|_, v| *v != idx);

        self.vec.pop_back()
    }

    /// Removes the back element and returns it alongside its key, if any,
    /// or `None` if the deqmap is empty.
    #[inline]
    pub fn pop_back_with_key(&mut self) -> Option<(Option<K>, V)>
    where
        K: Clone,
    {
        let idx = self.len() - 1;
        let key = self.find_key_unchecked(idx).cloned();
        if let Some(ref k) = key {
            self.map.remove_entry(k);
        };
        self.vec.pop_back().map(|v| (key, v))
    }

    /// Pushes an unkeyed `value` to the front (index 0).
    ///
    /// This operation updates all entries in the hashmap.
    ///
    /// # Examples
    /// ```
    /// # use deqmap::DeqMap;
    /// let mut qm: DeqMap<u8, u8> = DeqMap::new();
    /// qm.push_front(1);
    /// qm.push_front(2);
    /// assert_eq!(qm.front(), Some(&2));
    /// ```
    #[inline]
    pub fn push_front(&mut self, value: V) {
        self.vec.push_front(value);
        // update all the map values
        self.map.iter_mut().for_each(|(_k, v)| *v += 1);
    }

    /// Pushes an unkeyed `value` to the back and returns its index.
    #[inline]
    pub fn push_back(&mut self, value: V) -> usize {
        self.vec.push_back(value);
        self.vec.len() - 1
    }

    /// Inserts a `value` associated to a `key`, at the front of the collection.
    ///
    /// If the `key` doesn't already exist, proceeds with the insertion and
    /// returns `None`. Otherwise if the key exists, it remains unchanged and
    /// and returns the existing value.
    #[inline]
    pub fn insert_front(&mut self, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.map.get(&key) {
            // return existing
            self.vec.get(*idx)
        } else {
            // insert at the front
            self.vec.push_front(value);
            self.map.insert(key, 0);
            // update map indices
            self.map.iter_mut().for_each(|(_, i)| *i += 1);
            None
        }
    }

    /// Inserts a `value` associated to a `key`, at the back of the collection.
    ///
    /// If the `key` doesn't already exist, proceeds with the insertion and
    /// returns `None`. Otherwise if the key exists, it remains unchanged and
    /// and returns the existing value.
    #[inline]
    pub fn insert_back(&mut self, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.map.get(&key) {
            self.vec.get(*idx)
        } else {
            // insert at the back
            self.vec.push_back(value);
            self.map.insert(key, self.vec.len() - 1);
            None
        }
    }
}

/// # query, retrieval, insertion & removal by `key`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if the deqmap contains a value with the specified `key`.
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.contains_key(key)
    }

    /// Returns a reference to the value associated to the `key`.
    ///
    /// Returns `None` if there is no such key.
    #[inline]
    pub fn get_keyed<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(idx) = self.map.get(key) {
            self.vec.get(*idx)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value associated to the `key`.
    ///
    /// Returns `None` if there is no such key.
    #[inline]
    pub fn get_mut_keyed<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(idx) = self.map.get(key) {
            self.vec.get_mut(*idx)
        } else {
            None
        }
    }
}

/// # query, retrieval, insertion & removal by `index`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if there's a value at `index`.
    #[inline]
    pub fn has(&self, index: usize) -> bool {
        self.len() > index
    }

    /// Returns `true` if there's a value with an associated key at `index`.
    #[inline]
    pub fn has_key(&self, index: usize) -> bool {
        self.map.iter().any(|(_k, &i)| i == index)
    }

    /// Provides a reference to the value at `index`.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Result<&V> {
        self.vec.get(index).ok_or(Error::IndexOutOfBounds)
    }

    /// Provides a mutable reference to the value at `index`.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Result<&mut V> {
        self.vec.get_mut(index).ok_or(Error::IndexOutOfBounds)
    }

    /// Provides a reference to the value at `index` and to its associated key.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn get_with_key(&self, index: usize) -> Result<(Option<&K>, &V)> {
        if let Some(value) = self.vec.get(index) {
            let key = self.find_key(index)?;
            Ok((key, value))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides a mutable reference to the value at `index` and its associated
    /// key, if there is any.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn get_mut_with_key(&mut self, index: usize) -> Result<(Option<&K>, &mut V)> {
        if let Some(value) = self.vec.get_mut(index) {
            let key = self
                .map
                .iter_mut()
                .find_map(|(key, &mut idx)| if idx == index { Some(key) } else { None });
            Ok((key, value))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides a reference to the associated key at `index`, or `None`
    /// if there is no associated key.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn find_key(&self, index: usize) -> Result<Option<&K>> {
        if index < self.len() {
            Ok(self.find_key_unchecked(index))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides a reference to the associated key at `index`, or `None`
    /// if there is no associated key.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    #[inline]
    pub fn find_key_unchecked(&self, index: usize) -> Option<&K> {
        self.map
            .iter()
            .find_map(|(key, &i)| if i == index { Some(key) } else { None })
    }

    /// Provides a reference to the associated key, and the value at `index`, or
    /// `None` if there is no associated key.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    ///
    /// See also [`get_with_key`][Self#method.get_with_key], which always
    /// returns an existing value even if it has no associated key.
    #[inline]
    pub fn find_key_value(&self, index: usize) -> Result<Option<(&K, &V)>> {
        if index < self.len() {
            Ok(self.map.iter().find_map(|(key, &i)| {
                if i == index {
                    self.vec.get(i).map(|v| (key, v))
                } else {
                    None
                }
            }))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }
    // TODO: find_key_value unchecked

    /// Provides the associated key and mutable value at `index`, or `None`
    /// if there is no associated key.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    ///
    /// See also [`get_mut_with_key`][Self#method.get_mut_with_key], which
    /// always returns an existing value even if it has no associated key.
    #[inline]
    pub fn find_mut_key_value(&mut self, index: usize) -> Result<Option<(&K, &mut V)>> {
        if index < self.len() {
            Ok(
                if let Some(key) =
                    self.map
                        .iter_mut()
                        .find_map(|(key, &mut idx)| if idx == index { Some(key) } else { None })
                {
                    let value = self.vec.get_mut(index).unwrap();
                    Some((key, value))
                } else {
                    None
                },
            )
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }
    // TODO: find_key_value unchecked

    /// Pushes an unkeyed `value` at `index`.
    ///
    /// This operation cycles through all entries in the hashmap.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    #[inline]
    pub fn push_at(&mut self, index: usize, value: V) -> Result<()> {
        if index < self.len() {
            self.push_at_unchecked(index, value);
            Ok(())
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Pushes an unkeyed `value` at `index`.
    ///
    /// This operation cycles through all entries in the hashmap.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    #[inline]
    pub fn push_at_unchecked(&mut self, index: usize, value: V) {
        // inserting at `index` shifts the indices >= index
        self.vec.insert(index, value);
        // update existing map indices
        self.map.iter_mut().for_each(|(_, i)| {
            if *i >= index {
                *i += 1
            }
        });
    }

    /// Inserts a `key`ed `value` at `index`,
    /// shifting the columns with a greater index towards the back.
    ///
    /// Returns `None` on successful insertion.
    ///
    /// If the key already exists, the existing value will be returned unmodified.
    ///
    /// # Errors
    /// Errors if the index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// # use deqmap::DeqMap;
    ///
    /// let mut qm = DeqMap::from_iter(["v1", "v2"]);
    ///
    /// assert![matches![qm.insert_at(1, "k3", "v3"), Ok(None)]];
    /// assert_eq![qm.as_slice(), &["v1", "v3", "v2"]];
    ///
    /// // an existing key remains unmodified, exiting value is returned
    /// assert![matches![qm.insert_at(1, "k3", "v3_new"), Ok(Some(v)) if *v == "v3"]];
    /// // an out-of-bounds index returns an error
    /// assert![qm.insert_at(9, "k4", "v4").is_err()];
    /// ```
    #[inline]
    pub fn insert_at(&mut self, index: usize, key: K, value: V) -> Result<Option<&V>> {
        if index < self.len() {
            Ok(self.insert_at_unchecked(index, key, value))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Inserts a `key`ed `value` at `index`,
    /// shifting the columns with a greater index towards the back.
    ///
    /// Returns `None` on successful insertion.
    ///
    /// If the key already exists, the existing value will be returned unmodified.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    #[inline]
    pub fn insert_at_unchecked(&mut self, index: usize, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.map.get(&key) {
            self.vec.get(*idx)
        } else {
            // inserting at `index` shifts the indices >= index
            self.vec.insert(index, value);
            // update existing map indices before inserting the new one
            self.map.iter_mut().for_each(|(_, i)| {
                if *i >= index {
                    *i += 1
                }
            });
            self.map.insert(key, index);
            None
        }
    }

    /// Swaps elements at indices i and j.
    ///
    /// # Errors
    /// Errors if either index is out of bounds.
    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) -> Result<()> {
        if i < self.vec.len() && j < self.vec.len() {
            self.swap_unchecked(i, j);
            Ok(())
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }
    /// Swaps elements at indices `i` and `j`.
    ///
    /// # Panics
    /// Panics if either index is out of bounds.
    #[inline]
    pub fn swap_unchecked(&mut self, i: usize, j: usize) {
        self.vec.swap(i, j);
        for (_k, v) in self.map.iter_mut() {
            if *v == i {
                *v = j;
            } else if *v == j {
                *v = i;
            }
        }
    }
}

/// # query, retrieval, insertion & removal by `value`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if the deqmap contains an element with the given value.
    ///
    /// The operations is *O(n)*.
    pub fn contains(&self, value: &V) -> bool
    where
        V: PartialEq,
    {
        self.vec.contains(value)
    }

    /// Extends the deqmap with the provided iterator of `values`.
    #[inline]
    pub fn extend<I>(&mut self, values: I)
    where
        I: IntoIterator<Item = V>,
    {
        self.vec.extend(values);
    }

    /// Extends the deqmap with the provided iterator of `keys_values` pairs.
    ///
    /// If a key already exists, its associated value will get updated.
    pub fn extend_keyed<I>(&mut self, keys_values: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let (keys, values): (Vec<_>, Vec<_>) = keys_values.into_iter().unzip();

        // the index of the next new element
        let mut index = self.vec.len();

        for (k, v) in keys.into_iter().zip(values) {
            match self.map.entry(k) {
                // if the key already exists, just updates the value
                Entry::Occupied(_) => self.vec[index] = v,
                Entry::Vacant(e) => {
                    e.insert(index);
                    self.vec.push_back(v);
                    index += 1;
                }
            }
        }
    }
}

/// # iterators
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns an iterator over a slice of all the values,
    /// (and only the values).
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.vec.iter()
    }

    /// Returns a mutable iterator over a slice of all the values.
    /// (and only the values).
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.vec.iter_mut()
    }

    /// Returns an unordered iterator over just the keyed values, with keys.
    #[inline]
    pub fn iter_keyed(&self) -> impl Iterator<Item = (&K, &V)> {
        // SAFETY the entry should exist in the Vec
        self.map
            .iter()
            .map(|(k, idx)| (k, self.vec.get(*idx).unwrap()))
    }

    /// Returns an iterator over all the values, with their keys.
    ///
    /// # Examples
    /// ```
    /// # use deqmap::DeqMap;
    /// let mut v = DeqMap::new();
    /// v.insert_back("a", 1);
    /// v.push_back(2);
    ///
    /// let mut i = v.iter_with_keys();
    /// assert_eq![Some((Some(&"a"), &1)), i.next()];
    /// assert_eq![Some((None, &2)), i.next()];
    /// assert_eq![None, i.next()];
    /// ```
    #[inline]
    pub fn iter_with_keys(&self) -> DeqMapIter<'_, K, V> {
        DeqMapIter { qm: self, idx: 0 }
    }
}

impl<K, V> FromIterator<V> for DeqMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let mut qm = DeqMap::new();
        qm.extend(iter);
        qm
    }
}

impl<K, V> FromIterator<(K, V)> for DeqMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut qm = DeqMap::new();
        qm.extend_keyed(iter);
        qm
    }
}

/// An iterator over references to values and optional keys of a [`DeqMap`].
pub struct DeqMapIter<'qm, K, V>
where
    K: Hash + Eq,
{
    idx: usize,
    qm: &'qm DeqMap<K, V>,
}

impl<'qm, K, V> Iterator for DeqMapIter<'qm, K, V>
where
    K: Hash + Eq,
{
    type Item = (Option<&'qm K>, &'qm V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.qm.vec.get(self.idx).is_some() {
            self.idx += 1;
            self.qm.get_with_key(self.idx - 1).ok()
        } else {
            None
        }
    }
}

// FIXME:
// - https://stackoverflow.com/questions/72142637/iterator-next-method-lifetime-mismatch
// - https://stackoverflow.com/questions/63005820/how-do-i-fix-the-lifetime-mismatch-when-returning-a-mutable-reference-to-the-str
// - https://stackoverflow.com/questions/67414617/how-to-fix-lifetime-mismatch-when-implementing-iterator-trait
//
// /// An iterator over mutable references to values and optional keys of a [`DeqMap`].
// pub struct DeqMapIterMut<'qm, K, V>
// where
//     K: Hash + Eq,
// {
//     idx: usize,
//     qm: &'qm mut DeqMap<K, V>,
// }
//
// impl<'qm, 'a, K, V> Iterator for DeqMapIterMut<'qm, K, V>
// where
//     K: Hash + Eq,
// {
//     type Item = (Option<&'qm K>, &'qm mut V);
//     fn next(&'qm mut self) -> Option<Self::Item> {
//         // if let Some(v) = self.qm.vec.get(self.idx) {
//         if self.qm.vec.get(self.idx).is_some() { // IMPROVE
//             self.idx += 1;
//             self.qm.get_mut_with_key(self.idx -1)
//         } else {
//             None
//         }
//     }
// }
