// deqmap::deqmap
//
//!
//

use crate::{DeqMapError as Error, DeqMapResult as Result};
use core::{borrow::Borrow, hash::Hash};
use std::collections::{
    hash_map::{Entry, HashMap},
    VecDeque,
};

/// A double-ended queue with optional keys,
/// implemented a with [`VecDeque`] and a [`HashMap`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DeqMap<K: Hash + Eq, V> {
    vals: VecDeque<V>,
    keys: HashMap<K, usize>,
}

/// # general construction & configuration
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /* construct */

    /// Returns a new empty deqmap.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<&str, i32> = DeqMap::new();
    /// ```
    pub fn new() -> DeqMap<K, V> {
        DeqMap {
            vals: VecDeque::default(),
            keys: HashMap::default(),
        }
    }

    /// Converts an array of values `[V; N]` into a `DeqMap<_, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<&str, _> = DeqMap::from_array([1, 2, 3, 4]);
    /// ```
    pub fn from_array<const N: usize>(arr: [V; N]) -> DeqMap<K, V> {
        DeqMap {
            vals: VecDeque::from(arr),
            keys: HashMap::default(),
        }
    }

    /// Converts an array of keys and values `[(K, V); N]` into a `DeqMap<K, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let arr = [("b", 2), ("c", 3), ("d", 4), ("e", 5)];
    /// let dm = DeqMap::from_keyed_array(arr);
    /// ```
    pub fn from_keyed_array<const N: usize>(arr: [(K, V); N]) -> DeqMap<K, V> {
        let mut dm = Self::with_capacity(N, N);
        dm.extend_keyed(arr);
        dm
    }

    /// Converts a vec of values `Vec<V>` into a `DeqMap<_, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<&str, _> = DeqMap::from_vec(vec![1, 2, 3, 4]);
    /// ```
    pub fn from_vec(vec: Vec<V>) -> DeqMap<K, V> {
        DeqMap {
            vals: VecDeque::from(vec),
            keys: HashMap::default(),
        }
    }

    /// Converts a vec of keys and values `Vec<(K, V)>` into a `DeqMap<K, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let vec = vec![("b", 2), ("c", 3), ("d", 4), ("e", 5)];
    /// let dm = DeqMap::from_keyed_vec(vec);
    /// ```
    pub fn from_keyed_vec(vec: Vec<(K, V)>) -> DeqMap<K, V> {
        let mut dm = Self::with_capacity(vec.len(), vec.len());
        dm.extend_keyed(vec);
        dm
    }

    /// Returns a new empty `DeqMap`, with at least the specified capacity for
    /// `keys` and `values`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<u64, i32> = DeqMap::with_capacity(10, 30);
    /// assert![dm.capacity() >= (10, 30)];
    /// ```
    pub fn with_capacity(keys: usize, values: usize) -> DeqMap<K, V> {
        DeqMap {
            keys: HashMap::with_capacity(keys),
            vals: VecDeque::with_capacity(values),
        }
    }

    /// Returns a new empty `DeqMap`, with at least the specified `capacity` for
    /// just the values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm1: DeqMap<u64, i32> = DeqMap::with_capacity(10, 30);
    /// let dm2: DeqMap<u64, i32> = DeqMap::with_capacity_values(30);
    /// assert_eq![dm1.capacity_values(), dm2.capacity_values()];
    /// ```
    pub fn with_capacity_values(capacity: usize) -> DeqMap<K, V> {
        DeqMap {
            keys: HashMap::default(),
            vals: VecDeque::with_capacity(capacity),
        }
    }

    /* capacity */

    /// Returns the number of `(keys, values)` the deqmap can hold without
    /// reallocating.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<u64, i32> = DeqMap::with_capacity(10, 30);
    /// assert![dm.capacity().0 == dm.capacity_keys()];
    /// assert![dm.capacity().1 == dm.capacity_values()];
    /// ```
    #[inline]
    pub fn capacity(&self) -> (usize, usize) {
        (self.keys.capacity(), self.vals.capacity())
    }

    /// Returns the number of keys the deqmap can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<u64, i32> = DeqMap::with_capacity(10, 30);
    /// assert![dm.capacity_keys() >= 10];
    /// assert![dm.capacity_keys() < 30];
    /// ```
    #[inline]
    pub fn capacity_keys(&self) -> usize {
        self.keys.capacity()
    }

    /// Returns the number of values the deqmap can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<u64, i32> = DeqMap::with_capacity(10, 30);
    /// assert![dm.capacity_values() >= 30];
    /// ```
    #[inline]
    pub fn capacity_values(&self) -> usize {
        self.vals.capacity()
    }

    /* reserve */

    /// Reserves capacity for at least additional more `keys` and `values` to be
    /// inserted.
    ///
    /// # Panics
    /// Panics if either capacity overflows `usize`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = DeqMap::new();
    /// dm.reserve(10, 30);
    /// assert![dm.capacity() >= (10, 30)];
    /// ```
    #[inline]
    pub fn reserve(&mut self, keys: usize, values: usize) {
        self.keys.reserve(keys);
        self.vals.reserve(values);
    }

    /// Reserves capacity for at least `additional` more values to be inserted.
    ///
    /// # Panics
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = [1, 2].into();
    /// dm.reserve_values(30);
    /// assert![dm.capacity_values() >= 32];
    /// ```
    #[inline]
    pub fn reserve_values(&mut self, additional: usize) {
        self.vals.reserve(additional);
    }

    /// Reserves capacity for at least `additional` more keys to be inserted.
    ///
    /// # Panics
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = DeqMap::new();
    /// dm.reserve_keys(10);
    /// assert![dm.capacity_keys() >= 10];
    /// assert![dm.capacity_values() < 10];
    /// ```
    #[inline]
    pub fn reserve_keys(&mut self, additional: usize) {
        self.keys.reserve(additional);
    }

    /// Tries to reserve capacity for at least additional more `keys` and `values`
    /// to be inserted.
    /// The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `try_reserve`, capacity will be greater
    /// than or equal to `self.len() + additional` if it returns Ok(()).
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    /// If either capacity overflows, or the allocator reports a failure, then
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = DeqMap::new();
    /// if dm.try_reserve(10, 30).is_ok() {
    ///     assert![dm.capacity() >= (10, 30)];
    /// }
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, keys: usize, values: usize) -> Result<()> {
        self.keys.try_reserve(keys)?;
        self.vals.try_reserve(values)?;
        Ok(())
    }

    /// Tries to reserve capacity for at least `additional` more values to be inserted.
    /// The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `try_reserve_values`, capacity will be greater
    /// than or equal to `self.len_values() + additional` if it returns Ok(()).
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = DeqMap::new();
    /// if dm.try_reserve_values(30).is_ok() {
    ///     assert![dm.capacity_values() >= 30];
    /// }
    /// ```
    #[inline]
    pub fn try_reserve_values(&mut self, additional: usize) -> Result<()> {
        Ok(self.vals.try_reserve(additional)?)
    }

    /// Tries to reserve capacity for at least `additional` more keys to be inserted.
    /// The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `try_reserve_keys`, capacity will be greater
    /// than or equal to `self.len_keys() + additional` if it returns Ok(()).
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u64, i32> = DeqMap::new();
    /// if dm.try_reserve_keys(10).is_ok() {
    ///     assert![dm.capacity_keys() >= 10];
    /// }
    /// ```
    #[inline]
    pub fn try_reserve_keys(&mut self, additional: usize) -> Result<()> {
        Ok(self.keys.try_reserve(additional)?)
    }

    /* shrink */

    /// Shrinks the capacity of both keys and values as much as possible.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = DeqMap::with_capacity(7, 7);
    /// dm.extend(0..4);
    /// assert_eq![dm.capacity(), (7, 7)];
    /// dm.shrink_to_fit();
    /// assert![dm.capacity_keys() == 0];
    /// assert![dm.capacity_values() >= 4];
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.vals.shrink_to_fit();
        self.keys.shrink_to_fit();
    }

    /// Shrinks the capacity of just the values as much as possible.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = DeqMap::with_capacity(0, 15);
    /// dm.extend(0..4);
    /// assert_eq![dm.capacity_values(), 15];
    /// dm.shrink_to_fit();
    /// assert![dm.capacity_values() >= 4];
    /// assert![dm.capacity_values() < 15];
    /// ```
    #[inline]
    pub fn shrink_values_to_fit(&mut self) {
        self.vals.shrink_to_fit();
    }

    /// Shrinks the capacity of just the keys as much as possible.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(14, 4);
    /// dm.extend_keyed([("a", 1), ("b", 2), ("c", 3), ("d", 4)].into_iter());
    /// assert_eq![dm.capacity_keys(), 14];
    /// dm.shrink_to_fit();
    /// assert![dm.capacity_keys() >= 4];
    /// assert![dm.capacity_keys() < 14];
    /// ```
    #[inline]
    pub fn shrink_keys_to_fit(&mut self) {
        self.keys.shrink_to_fit();
    }

    /// Shrinks the capacity of both keys and values, with a lower limit.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = DeqMap::with_capacity(14, 15);
    /// dm.extend(0..4);
    /// assert_eq![dm.capacity(), (14, 15)];
    /// dm.shrink_to(6);
    /// assert![dm.capacity() >= (6, 6)];
    /// assert![dm.capacity() < (14, 15)];
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.vals.shrink_to(min_capacity);
        self.keys.shrink_to(min_capacity);
    }

    /// Shrinks the capacity of just the values, with a lower limit.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = DeqMap::with_capacity(14, 15);
    /// dm.extend(0..4);
    /// assert_eq![dm.capacity_values(), 15];
    /// dm.shrink_values_to(6);
    /// assert![dm.capacity_values() >= 6];
    /// assert![dm.capacity_values() < 15];
    /// assert_eq![dm.capacity_keys(), 14];
    /// ```
    #[inline]
    pub fn shrink_values_to(&mut self, min_capacity: usize) {
        self.vals.shrink_to(min_capacity);
    }

    /// Shrinks the capacity of just the keys, with a lower limit.
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = DeqMap::with_capacity(14, 15);
    /// dm.extend_keyed([("a", 1), ("b", 2)]);
    /// assert_eq![dm.capacity_keys(), 14];
    /// dm.shrink_keys_to(6);
    /// assert![dm.capacity_keys() >= 6];
    /// assert![dm.capacity_keys() < 14];
    /// assert![dm.capacity_values() == 15];
    /// ```
    #[inline]
    pub fn shrink_keys_to(&mut self, min_capacity: usize) {
        self.keys.shrink_to(min_capacity);
    }

    /* slicing */

    /// Returns a slice of the values, in order.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u32, u8> = DeqMap::from([3, 4]);
    /// assert_eq![dm.as_mut_slice(), &[3, 4]];
    /// ```
    #[inline]
    pub fn as_slice(&mut self) -> &[V] {
        self.vals.make_contiguous();
        self.vals.as_slices().0
    }

    /// Returns a mutable slice of the values, in order.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u32, u8> = [3, 4].into();
    /// assert_eq![dm.as_mut_slice(), &mut [3, 4]];
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [V] {
        self.vals.make_contiguous()
    }

    // /// Rearranges the internal storage of the internal deque of values
    // /// so it is one contiguous slice, which is then returned.
    // #[inline]
    // pub fn make_contiguous(&mut self) -> &mut [V] {
    //     self.vals.make_contiguous()
    // }
    //
    // /// Returns a pair of slices which contain, in order,
    // /// references of the internal deque of values.
    // ///
    // /// If [`make_contiguous`][Self::make_contiguous] was previously called, all
    // /// elements will be in the first slice and the second slice will be empty.
    // #[inline]
    // pub fn as_slices(&mut self) -> (&[V], &[V]) {
    //     self.vals.as_slices()
    // }
    //
    // /// Returns a pair of slices which contain, in order,
    // /// mutable references of the internal deque of values.
    // ///
    // /// If [`make_contiguous`][Self::make_contiguous] was previously called, all
    // /// elements will be in the first slice and the second slice will be empty.
    // #[inline]
    // pub fn as_mut_slices(&mut self) -> (&mut[V], &mut [V]) {
    //     self.vals.as_mut_slices()
    // }
}

/// # general query, retrieval, insertion & removal
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns the number of (keys, values).
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, u8> = [3].into();
    /// dm.insert_back("five", 5);
    /// assert_eq![dm.len(), (1, 2)];
    /// ```
    #[inline]
    pub fn len(&self) -> (usize, usize) {
        (self.keys.len(), self.vals.len())
    }

    /// Returns the number of values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, u8> = [3, 4].into();
    /// assert_eq![dm.len_values(), 2];
    /// ```
    #[inline]
    pub fn len_values(&self) -> usize {
        self.vals.len()
    }

    /// Returns the number of keys.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from_keyed_vec(vec![("c", 3), ("d", 4)]);
    /// assert_eq![dm.len_keys(), 2];
    /// ```
    #[inline]
    pub fn len_keys(&self) -> usize {
        self.keys.len()
    }

    /// Returns `true` if there are no values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, i32> = DeqMap::new();
    /// assert_eq![dm.is_empty(), true];
    ///
    /// dm.push_back(1);
    /// assert_eq![dm.is_empty(), false];
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }

    /// Returns `true` if there are no keys.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, i32> = DeqMap::new();
    /// dm.push_back(1);
    /// assert_eq![dm.has_no_keys(), true];
    ///
    /// dm.insert_back("key", 2);
    /// assert_eq![dm.has_no_keys(), false];
    /// ```
    #[inline]
    pub fn has_no_keys(&self) -> bool {
        self.keys.is_empty()
    }

    /// Returns the index of the value at the back, or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, i32>::new();
    /// assert_eq![dm.back_index(), None];
    ///
    /// dm.push_back(1);
    /// assert_eq![dm.back_index(), Some(0)];
    /// ```
    #[inline]
    pub fn back_index(&self) -> Option<usize> {
        let len = self.vals.len();
        if len > 0 {
            Some(len - 1)
        } else {
            None
        }
    }

    /// Clears the deqmap, removing all values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from_keyed_vec(vec![("c", 3), ("d", 4)]);
    /// assert_eq![dm.len(), (2, 2)];
    ///
    /// dm.clear();
    /// assert_eq![dm.len(), (0, 0)];
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vals.clear();
        self.keys.clear();
    }

    /// Removes all the keys, leaves the values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, i32>::from([("c", 3), ("d", 4)]);
    /// assert_eq![dm.len(), (2, 2)];
    ///
    /// dm.clear_keys();
    /// assert_eq![dm.len(), (0, 2)];
    /// ```
    #[inline]
    pub fn clear_keys(&mut self) {
        self.keys.clear();
    }

    /// Provides a reference to the front element,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm: DeqMap<&str, _> = [3, 4].into();
    /// assert_eq![dm.front(), Some(&3)];
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&V> {
        self.vals.front()
    }

    /// Provides a mutable reference to the front element,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = [3, 4].into();
    /// assert_eq![dm.front_mut(), Some(&mut 3)];
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut V> {
        self.vals.front_mut()
    }

    /// Provides a reference to the front element, alongside its key, if any,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// assert_eq![dm.front_with_key(), Some((Some(&"c"), &3))];
    /// ```
    #[inline]
    pub fn front_with_key(&self) -> Option<(Option<&K>, &V)> {
        self.get_with_key(0).ok()
    }

    /// Provides a mutable reference to the front element, alongside its key,
    /// if any, or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// assert_eq![dm.front_mut_with_key(), Some((Some(&"c"), &mut 3))];
    /// ```
    #[inline]
    pub fn front_mut_with_key(&mut self) -> Option<(Option<&K>, &mut V)> {
        self.get_mut_with_key(0).ok()
    }

    /// Provides a reference to the back element,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = [3, 4].into();
    /// assert_eq![dm.back(), Some(&4)];
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&V> {
        self.vals.back()
    }

    /// Provides a mutable reference to the back element,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = [3, 4].into();
    /// assert_eq![dm.back_mut(), Some(&mut 4)];
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut V> {
        self.vals.back_mut()
    }

    /// Provides a reference to the back element, alongside its key, if any,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// assert_eq![dm.back_with_key(), Some((Some(&"d"), &4))];
    /// ```
    #[inline]
    pub fn back_with_key(&self) -> Option<(Option<&K>, &V)> {
        self.get_with_key(self.back_index()?).ok()
    }

    /// Provides a mutable reference to the back element, alongside its key,
    /// if any, or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// assert_eq![dm.back_mut_with_key(), Some((Some(&"d"), &mut 4))];
    /// ```
    #[inline]
    pub fn back_mut_with_key(&mut self) -> Option<(Option<&K>, &mut V)> {
        self.get_mut_with_key(self.back_index()?).ok()
    }

    /// Removes the front element and returns it, or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = [3, 4].into();
    ///
    /// assert_eq![dm.pop_front(), Some(3)];
    /// assert_eq![dm.pop_front(), Some(4)];
    /// assert_eq![dm.pop_front(), None];
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<V> {
        self.keys.retain(|_, v| {
            // retain and and update the entries with values > 0
            if *v == 0 {
                false
            } else {
                *v -= 1;
                true
            }
        });
        self.vals.pop_front()
    }

    /// Removes the front element and returns it alongside its key, if any,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// dm.push_back(5);
    ///
    /// assert_eq![dm.pop_front_with_key(), Some((Some("c"), 3))];
    /// assert_eq![dm.pop_front_with_key(), Some((Some("d"), 4))];
    /// assert_eq![dm.pop_front_with_key(), Some((None, 5))];
    /// assert_eq![dm.pop_front_with_key(), None];
    /// ```
    #[inline]
    pub fn pop_front_with_key(&mut self) -> Option<(Option<K>, V)>
    where
        K: Clone,
    {
        const IDX: usize = 0;
        let key = self.find_key_unchecked(IDX).cloned();
        // retain and update the entries with values > idx
        self.keys.retain(|_, v| {
            if *v == IDX {
                false
            } else {
                *v -= 1;
                true
            }
        });
        self.vals.pop_front().map(|v| (key, v))
    }

    /// Removes the back element and returns it, or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<&str, _> = [3, 4].into();
    ///
    /// assert_eq![dm.pop_back(), Some(4)];
    /// assert_eq![dm.pop_back(), Some(3)];
    /// assert_eq![dm.pop_back(), None];
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<V> {
        // remove any keyed entry pointing to the last value.
        let idx = self.back_index()?;
        self.keys.retain(|_, v| *v != idx);
        self.vals.pop_back()
    }

    /// Removes the back element and returns it alongside its key, if any,
    /// or `None` if the deqmap is empty.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("c", 3), ("d", 4)]);
    /// dm.push_front(2);
    ///
    /// assert_eq![dm.pop_back_with_key(), Some((Some("d"), 4))];
    /// assert_eq![dm.pop_back_with_key(), Some((Some("c"), 3))];
    /// assert_eq![dm.pop_back_with_key(), Some((None, 2))];
    /// assert_eq![dm.pop_back_with_key(), None];
    /// ```
    #[inline]
    pub fn pop_back_with_key(&mut self) -> Option<(Option<K>, V)>
    where
        K: Clone,
    {
        let idx = self.back_index()?;
        let key = self.find_key_unchecked(idx).cloned();
        if let Some(ref k) = key {
            self.keys.remove_entry(k);
        };
        self.vals.pop_back().map(|v| (key, v))
    }

    /// Pushes an unkeyed `value` to the front (index 0).
    ///
    /// This operation updates all entries in the hashmap.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u8, u8> = DeqMap::from([1]);
    /// dm.push_front(2);
    /// assert_eq!(dm.front(), Some(&2));
    /// assert_eq!(dm.back(), Some(&1));
    /// ```
    #[inline]
    pub fn push_front(&mut self, value: V) {
        self.vals.push_front(value);
        // update all the map values
        self.keys.iter_mut().for_each(|(_k, v)| *v += 1);
    }

    /// Pushes an unkeyed `value` to the back and returns its index.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm: DeqMap<u8, u8> = DeqMap::from([1]);
    /// dm.push_back(2);
    /// assert_eq!(dm.front(), Some(&1));
    /// assert_eq!(dm.back(), Some(&2));
    /// ```
    #[inline]
    pub fn push_back(&mut self, value: V) -> usize {
        self.vals.push_back(value);
        self.vals.len() - 1
    }

    /// Inserts a `value` associated to a `key`, at the front of the collection.
    ///
    /// If the `key` doesn't already exist, proceeds with the insertion and
    /// returns `None`. Otherwise if the key exists, it remains unchanged and
    /// and returns the existing value.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1)]);
    /// dm.insert_front("b", 2);
    /// assert_eq!(dm.front(), Some(&2));
    /// assert_eq!(dm.back(), Some(&1));
    /// ```
    #[inline]
    pub fn insert_front(&mut self, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.keys.get(&key) {
            // return existing
            self.vals.get(*idx)
        } else {
            // insert at the front
            self.vals.push_front(value);
            self.keys.insert(key, 0);
            // update map indices
            self.keys.iter_mut().for_each(|(_, i)| *i += 1);
            None
        }
    }

    /// Inserts a `value` associated to a `key`, at the back of the collection.
    ///
    /// If the `key` doesn't already exist, proceeds with the insertion and
    /// returns `None`. Otherwise if the key exists, it remains unchanged and
    /// and returns the existing value.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1)]);
    /// dm.insert_back("b", 2);
    /// assert_eq!(dm.front(), Some(&1));
    /// assert_eq!(dm.back(), Some(&2));
    /// ```
    #[inline]
    pub fn insert_back(&mut self, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.keys.get(&key) {
            self.vals.get(*idx)
        } else {
            // insert at the back
            self.vals.push_back(value);
            self.keys.insert(key, self.vals.len() - 1);
            None
        }
    }
}

/// # query, retrieval, insertion & removal by `key`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if the deqmap contains a value with the specified `key`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.contains_key(&"b"), true];
    /// assert_eq![dm.contains_key(&"f"), false];
    /// ```
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.keys.contains_key(key)
    }

    /// Returns the index of the value associated to the `key`.
    ///
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.get_index(&"b"), Some(1)];
    /// ```
    #[inline]
    pub fn get_index<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.keys.get(key).copied()
    }

    /// Returns a reference to the value associated to the `key`.
    ///
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.get_keyed(&"b"), Some(&2)];
    /// ```
    #[inline]
    pub fn get_keyed<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(idx) = self.keys.get(key) {
            self.vals.get(*idx)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value associated to the `key`.
    ///
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.get_mut_keyed(&"b"), Some(&mut 2)];
    /// ```
    #[inline]
    pub fn get_mut_keyed<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(idx) = self.keys.get(key) {
            self.vals.get_mut(*idx)
        } else {
            None
        }
    }

    /// Resets the `old_key` associated with a value, to `new_key`.
    ///
    /// On success returns `true`. Otherwise, if the `old_key` doesn't exists,
    /// it does nothing and returns `false`.
    ///
    /// See also [`set_key`][Self::set_key].
    ///
    /// # Errors
    /// Errors if `new_key` already exists.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1), ("b", 2), ("c", 3)]);
    ///
    /// assert_eq![dm.reset_key("a", "A"), Ok(true)];
    /// assert_eq![dm.reset_key("d", "D"), Ok(false)];
    /// assert![dm.reset_key("c", "b").is_err()];
    ///
    /// assert_eq![dm.get_keyed("A"), Some(&1)];
    /// assert_eq![dm.get_keyed("b"), Some(&2)];
    /// assert_eq![dm.get_keyed("c"), Some(&3)];
    /// assert_eq![dm.get_keyed("D"), None];
    /// ```
    pub fn reset_key<Q>(&mut self, old_key: &Q, new_key: K) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if self.contains_key(new_key.borrow()) {
            Err(Error::KeyAlreadyExists)
        } else if let Some(v) = self.keys.remove(old_key) {
            self.keys.insert(new_key, v);
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

/// # query, retrieval, insertion & removal by `index`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if there is a value at `index`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::{DeqMap, DeqMapError};
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([1, 2]);
    /// assert_eq![dm.is_at(0), true];
    /// assert_eq![dm.is_at(2), false];
    /// ```
    #[inline]
    pub fn is_at(&self, index: usize) -> bool {
        self.len_values() > index
    }

    /// Returns `true` if there is a value at `index`, with an associated key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::{DeqMap, DeqMapError};
    ///
    /// let mut dm = DeqMap::from([1, 2, 3]);
    /// dm.set_key(0, "a");
    /// assert_eq![dm.is_keyed_at(0), true];
    /// assert_eq![dm.is_keyed_at(1), false];
    /// ```
    #[inline]
    pub fn is_keyed_at(&self, index: usize) -> bool {
        self.keys.iter().any(|(_k, &i)| i == index)
    }

    /// Provides a reference to the value at `index`.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::{DeqMap, DeqMapError};
    ///
    /// let mut dm = DeqMap::<&str, _>::from([1, 2, 3]);
    /// assert_eq![dm.get(2), Ok(&3)];
    /// assert![dm.get(3).is_err()];
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Result<&V> {
        self.vals.get(index).ok_or(Error::IndexOutOfBounds)
    }

    /// Provides a mutable reference to the value at `index`.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::{DeqMap, DeqMapError};
    ///
    /// let mut dm = DeqMap::<&str, _>::from([1, 2, 3]);
    /// assert_eq![dm.get_mut(0), Ok(&mut 1)];
    /// assert![dm.get(3).is_err()];
    /// ```
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Result<&mut V> {
        self.vals.get_mut(index).ok_or(Error::IndexOutOfBounds)
    }

    /// Provides a reference to the value at `index` and to its associated key.
    ///
    /// See also [`find_key_value`][Self::find_key_value], which wont return
    /// the value if it has no associated key.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([1, 2]);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.get_with_key(1), Ok((None, &2))];
    /// assert_eq![dm.get_with_key(2), Ok((Some(&"c"), &3))];
    /// assert![dm.get_with_key(3).is_err()];
    /// ```
    #[inline]
    pub fn get_with_key(&self, index: usize) -> Result<(Option<&K>, &V)> {
        if let Some(value) = self.vals.get(index) {
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
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([1, 2]);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.get_mut_with_key(1), Ok((None, &mut 2))];
    /// assert_eq![dm.get_mut_with_key(2), Ok((Some(&"c"), &mut 3))];
    /// assert![dm.get_mut_with_key(3).is_err()];
    /// ```
    #[inline]
    pub fn get_mut_with_key(&mut self, index: usize) -> Result<(Option<&K>, &mut V)> {
        if let Some(value) = self.vals.get_mut(index) {
            let key = self
                .keys
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
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_key(0), Ok(None)];
    /// assert_eq![dm.find_key(2), Ok(Some(&"c"))];
    /// assert![dm.find_key(3).is_err()];
    /// ```
    #[inline]
    pub fn find_key(&self, index: usize) -> Result<Option<&K>> {
        if index < self.len_values() {
            Ok(self.find_key_unchecked(index))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides a reference to the associated key at `index`, or `None`
    /// if there is no associated key.
    ///
    /// # Panics
    /// Panics if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_key_unchecked(0), None];
    /// assert_eq![dm.find_key_unchecked(2), Some(&"c")];
    /// ```
    #[inline]
    pub fn find_key_unchecked(&self, index: usize) -> Option<&K> {
        self.keys
            .iter()
            .find_map(|(key, &i)| if i == index { Some(key) } else { None })
    }

    /// Provides a reference to the associated key, and the value at `index`,
    /// or `None` if there is no associated key.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// See also [`get_with_key`][Self::get_with_key], which always
    /// returns an existing value even if it has no associated key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_key_value(0), Ok(None)];
    /// assert_eq![dm.find_key_value(2), Ok(Some((&"c", &3)))];
    /// assert![dm.find_key_value(3).is_err()];
    /// ```
    #[inline]
    pub fn find_key_value(&self, index: usize) -> Result<Option<(&K, &V)>> {
        if index < self.len_values() {
            Ok(self.find_key_value_unchecked(index))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides a reference to the associated key, and the value at `index`,
    /// or `None` if there is no associated key.
    ///
    /// # Panics
    /// Panics if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_key_value_unchecked(0), None];
    /// assert_eq![dm.find_key_value_unchecked(2), Some((&"c", &3))];
    /// ```
    #[inline]
    pub fn find_key_value_unchecked(&self, index: usize) -> Option<(&K, &V)> {
        self.keys.iter().find_map(|(key, &i)| {
            if i == index {
                self.vals.get(i).map(|v| (key, v))
            } else {
                None
            }
        })
    }

    /// Provides the associated key and mutable value at `index`,
    /// or `None` if there is no associated key.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// See also [`get_mut_with_key`][Self::get_mut_with_key], which
    /// always returns an existing value even if it has no associated key.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_mut_key_value(0), Ok(None)];
    /// assert_eq![dm.find_mut_key_value(2), Ok(Some((&"c", &mut 3)))];
    /// assert![dm.find_key_value(3).is_err()];
    /// ```
    #[inline]
    pub fn find_mut_key_value(&mut self, index: usize) -> Result<Option<(&K, &mut V)>> {
        if index < self.len_values() {
            Ok(self.find_mut_key_value_unchecked(index))
        } else {
            Err(Error::IndexOutOfBounds)
        }
    }

    /// Provides the associated key and mutable value at `index`,
    /// or `None` if there is no associated key.
    ///
    /// # Panics
    /// Panics if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::with_capacity(2, 3);
    /// dm.push_back(1);
    /// dm.insert_back("b", 2);
    /// dm.insert_back("c", 3);
    ///
    /// assert_eq![dm.find_mut_key_value_unchecked(0), None];
    /// assert_eq![dm.find_mut_key_value_unchecked(2), Some((&"c", &mut 3))];
    /// ```
    #[inline]
    pub fn find_mut_key_value_unchecked(&mut self, index: usize) -> Option<(&K, &mut V)> {
        if let Some(key) =
            self.keys
                .iter_mut()
                .find_map(|(key, &mut idx)| if idx == index { Some(key) } else { None })
        {
            let value = self.vals.get_mut(index).unwrap();
            Some((key, value))
        } else {
            None
        }
    }

    /// Pushes an unkeyed `value` at `index`.
    ///
    /// This operation cycles through all entries in the hashmap.
    ///
    /// # Errors
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u16>::from([1, 2, 3]);
    ///
    /// assert![dm.push_at(3, 300).is_err()];
    /// assert![dm.push_at(2, 200).is_ok()];
    ///
    /// assert_eq![dm.as_slice(), &[1, 2, 200, 3]];
    /// ```
    #[inline]
    pub fn push_at(&mut self, index: usize, value: V) -> Result<()> {
        if index < self.len_values() {
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
    /// Panics if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u16>::from([1, 2, 3]);
    ///
    /// dm.push_at_unchecked(2, 200);
    /// assert_eq![dm.get(2), Ok(&200)];
    /// ```
    #[inline]
    pub fn push_at_unchecked(&mut self, index: usize, value: V) {
        // inserting at `index` shifts the indices >= index
        self.vals.insert(index, value);
        // update existing map indices
        self.keys.iter_mut().for_each(|(_, i)| {
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
    /// Errors if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from(["v1", "v2"]);
    ///
    /// assert![matches![dm.insert_at(1, "k3", "v3"), Ok(None)]];
    /// assert_eq![dm.as_slice(), &["v1", "v3", "v2"]];
    ///
    /// // an existing key remains unmodified, exiting value is returned
    /// assert![matches![dm.insert_at(1, "k3", "v3_new"), Ok(Some(v)) if *v == "v3"]];
    /// // an out-of-bounds index returns an error
    /// assert![dm.insert_at(9, "k4", "v4").is_err()];
    /// ```
    #[inline]
    pub fn insert_at(&mut self, index: usize, key: K, value: V) -> Result<Option<&V>> {
        if index < self.len_values() {
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
    /// Panics if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from(["v1", "v2"]);
    ///
    /// assert![matches![dm.insert_at_unchecked(1, "k3", "v3"), None]];
    /// assert_eq![dm.as_slice(), &["v1", "v3", "v2"]];
    ///
    /// // an existing key remains unmodified, exiting value is returned
    /// assert![matches![dm.insert_at_unchecked(1, "k3", "v3_new"), Some(v) if *v == "v3"]];
    /// ```
    #[inline]
    pub fn insert_at_unchecked(&mut self, index: usize, key: K, value: V) -> Option<&V> {
        if let Some(idx) = self.keys.get(&key) {
            self.vals.get(*idx)
        } else {
            // inserting at `index` shifts the indices >= index
            self.vals.insert(index, value);
            // update existing map indices before inserting the new one
            self.keys.iter_mut().for_each(|(_, i)| {
                if *i >= index {
                    *i += 1
                }
            });
            self.keys.insert(key, index);
            None
        }
    }

    /* retain */

    /// Retains only the elements specified by the predicate over the values.
    ///
    /// In other words, remove all values `v` for which `f(&v)` returns false,
    /// along with their keys, if any.
    ///
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// This operation is slow, since it first allocates the retained indexes
    /// and then iterates over the keys to update them.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    ///
    /// dm.retain(|&v| v == 3);
    /// assert_eq![dm.as_slice(), &[3]];
    /// assert_eq![dm.len(), (1, 1)];
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate over the values.
    ///
    /// In other words, remove all values `v` for which `f(&v)` returns false,
    /// along with their keys, if any.
    ///
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// This operation is slow, because it allocates the retained indexes and
    /// then iterates over the keys in order to retain and update them.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::from([("a", 1), ("b", 2), ("c", 3)]);
    ///
    /// dm.retain_mut(|v| if *v == 3 {
    ///     *v += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq![dm.as_slice(), &[4]];
    /// assert_eq![dm.len(), (1, 1)];
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut V) -> bool,
    {
        // based on:
        // https://doc.rust-lang.org/1.64.0/src/alloc/collections/vec_deque/mod.rs.html#2225

        let mut mapretain = vec![];
        let mut mapchange = vec![];

        let len = self.vals.len();
        let mut idx = 0;
        let mut cur = 0;

        // Stage 1: All values are retained.
        while cur < len {
            if !f(&mut self.vals[cur]) {
                cur += 1;
                break;
            }
            cur += 1;
            idx += 1;
        }
        // Stage 2: Swap retained value into current idx.
        while cur < len {
            if !f(&mut self.vals[cur]) {
                cur += 1;
                continue;
            }

            // save the indexes to determine which keys to retain
            mapretain.push(cur);
            mapchange.push((cur, idx));

            self.vals.swap(idx, cur);
            cur += 1;
            idx += 1;
        }
        // Stage 3: Truncate all values after idx.
        if cur != idx {
            self.vals.truncate(idx);
        }
        // Stage 4: retain the associated keys
        self.keys.retain(|_, &mut ival| {
            if let Some(idx) = mapretain.iter().position(|e| e == &ival) {
                // removes value for shorter subsequent loops
                mapretain.swap_remove(idx);
                true
            } else {
                false
            }
        });
        // Stage 5: update the keys
        self.keys.iter_mut().for_each(|(_k, v)| {
            let mut idx = 0;
            while idx < mapchange.len() {
                let (pre_idx, new_idx) = mapchange[idx];
                if *v == pre_idx {
                    *v = new_idx;
                    // ensure shorter subsequent loops
                    mapchange.swap_remove(idx);
                    break;
                }
                idx += 1;
            }
        });
    }

    /* truncate */

    /// Shortens the deqmap, keeping the first `len` values and dropping the rest.
    ///
    /// If `len` is greater than the current `len_values`, this has no effect.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.len_values(), 3];
    ///
    /// dm.truncate(2);
    /// assert_eq![dm.len_values(), 2];
    /// assert_eq![dm.pop_back_with_key(), Some((Some("b"), 2))];
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len <= self.vals.len() {
            self.vals.truncate(len);
            self.keys.retain(|_, v| *v <= len);
        }
    }

    /* swap */

    /// Swaps elements at indices `i` and `j`.
    ///
    /// # Errors
    /// Errors if either index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    ///
    /// assert![dm.swap(0, 2).is_ok()];
    /// assert_eq![dm.get_with_key(0), Ok((Some(&"c"), &3))];
    /// assert_eq![dm.get_with_key(2), Ok((Some(&"a"), &1))];
    /// assert![dm.swap(0, 7).is_err()];
    /// ```
    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) -> Result<()> {
        if i < self.vals.len() && j < self.vals.len() {
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
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    ///
    /// dm.swap_unchecked(0, 2);
    /// assert_eq![dm.get_with_key(0), Ok((Some(&"c"), &3))];
    /// assert_eq![dm.get_with_key(2), Ok((Some(&"a"), &1))];
    /// ```
    #[inline]
    pub fn swap_unchecked(&mut self, i: usize, j: usize) {
        self.vals.swap(i, j);

        // Update the map, breaking the loop early if we can
        let mut counter = 2;
        for (_k, v) in self.keys.iter_mut() {
            if *v == i {
                *v = j;
                counter -= 1;
            } else if *v == j {
                *v = i;
                counter -= 1;
            }
            if counter == 0 {
                break;
            }
        }
    }

    /* set key */

    /// Sets the `key` associated with a value at `index`.
    ///
    /// Returns the old key if there was any, or `None` otherwise.
    ///
    /// See also [`reset_key`][Self::reset_key].
    ///
    /// # Errors
    /// Errors if the `key` already exists, or if the `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use deqmap::{DeqMap, DeqMapError};
    ///
    /// let mut dm = DeqMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// dm.push_back(4);
    ///
    /// assert_eq![dm.set_key(0, "A"), Ok(Some("a"))];
    /// assert_eq![dm.set_key(3, "d"), Ok(None)];
    /// assert_eq![dm.set_key(2, "b"), Err(DeqMapError::KeyAlreadyExists)];
    /// assert_eq![dm.set_key(6, "f"), Err(DeqMapError::IndexOutOfBounds)];
    ///
    /// assert_eq![dm.get_keyed("A"), Some(&1)];
    /// assert_eq![dm.get_keyed("b"), Some(&2)];
    /// assert_eq![dm.get_keyed("c"), Some(&3)];
    /// assert_eq![dm.get_keyed("d"), Some(&4)];
    /// ```
    pub fn set_key(&mut self, index: usize, key: K) -> Result<Option<K>>
    where
        K: Clone,
    {
        if self.contains_key(&key) {
            Err(Error::KeyAlreadyExists)
        } else {
            let old_key = self.find_key(index)?.cloned();

            if let Some(ref k) = old_key {
                self.keys.remove(k.borrow());
            };

            self.keys.insert(key, index);
            Ok(old_key)
        }
    }
}

/// # query, retrieval, insertion & removal by `value`
impl<K: Hash + Eq, V> DeqMap<K, V> {
    /// Returns `true` if the deqmap contains an element with the given value.
    ///
    /// The operations is *O(n)*.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, _>::from([1, 2, 3]);
    ///
    /// assert_eq![dm.contains(&2), true];
    /// assert_eq![dm.contains(&5), false];
    /// ```
    pub fn contains(&self, value: &V) -> bool
    where
        V: PartialEq,
    {
        self.vals.contains(value)
    }

    /// Extends the deqmap with the provided iterator of `values`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::<&str, u8>::new();
    ///
    /// dm.extend(0..5);
    /// assert_eq![dm.as_slice(), &[0, 1, 2, 3, 4]];
    /// ```
    #[inline]
    pub fn extend<I>(&mut self, values: I)
    where
        I: IntoIterator<Item = V>,
    {
        self.vals.extend(values);
    }

    /// Extends the deqmap with the provided iterator of `keys_values` pairs.
    ///
    /// If a key already exists, its associated value will get updated.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut dm = DeqMap::new();
    ///
    /// dm.extend_keyed([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq![dm.find_key_value(0), Ok(Some((&"a", &1)))];
    /// assert_eq![dm.find_key_value(1), Ok(Some((&"b", &2)))];
    /// assert_eq![dm.find_key_value(2), Ok(Some((&"c", &3)))];
    /// ```
    pub fn extend_keyed<I>(&mut self, keys_values: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let (keys, values): (Vec<_>, Vec<_>) = keys_values.into_iter().unzip();

        // the index of the next new element
        let mut index = self.vals.len();

        for (k, v) in keys.into_iter().zip(values) {
            match self.keys.entry(k) {
                // if the key already exists, just updates the value
                Entry::Occupied(_) => self.vals[index] = v,
                Entry::Vacant(e) => {
                    e.insert(index);
                    self.vals.push_back(v);
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
        self.vals.iter()
    }

    /// Returns a mutable iterator over a slice of all the values.
    /// (and only the values).
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.vals.iter_mut()
    }

    /// Returns an **unordered** iterator of (key, value) over the keyed values.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let mut v = DeqMap::new();
    /// v.insert_back(-1, 1);
    /// v.push_back(2);
    /// v.insert_back(-3, 3);
    /// v.push_back(4);
    ///
    /// let mut vec: Vec<(&i8, &u8)> = v.iter_keyed().collect();
    /// vec.sort();
    /// assert_eq![vec, vec![(&-3, &3), (&-1, &1)]];
    /// ```
    #[inline]
    pub fn iter_keyed(&self) -> impl Iterator<Item = (&K, &V)> {
        // SAFETY: methods ensure each key points to a valid index
        self.keys
            .iter()
            .map(|(k, idx)| (k, self.vals.get(*idx).unwrap()))
    }

    /// Returns an iterator over all the values, with their keys.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
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
        DeqMapIter { dm: self, idx: 0 }
    }
}

impl<K, V> FromIterator<V> for DeqMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let mut dm = DeqMap::new();
        dm.extend(iter);
        dm
    }
}

impl<K, V> FromIterator<(K, V)> for DeqMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut dm = DeqMap::new();
        dm.extend_keyed(iter);
        dm
    }
}

/// An iterator over references to values and optional keys of a [`DeqMap`].
pub struct DeqMapIter<'dm, K, V>
where
    K: Hash + Eq,
{
    idx: usize,
    dm: &'dm DeqMap<K, V>,
}

impl<'dm, K, V> Iterator for DeqMapIter<'dm, K, V>
where
    K: Hash + Eq,
{
    type Item = (Option<&'dm K>, &'dm V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.dm.vals.get(self.idx).is_some() {
            self.idx += 1;
            self.dm.get_with_key(self.idx - 1).ok()
        } else {
            None
        }
    }
}

// FIXME:
// /// An iterator over mutable references to values and optional keys of a [`DeqMap`].
// pub struct DeqMapIterMut<'dm, K, V>
// where
//     K: Hash + Eq,
// {
//     idx: usize,
//     dm: &'dm mut DeqMap<K, V>,
// }
//
// impl<'dm, 'a, K, V> Iterator for DeqMapIterMut<'dm, K, V>
// where
//     K: Hash + Eq,
// {
//     type Item = (Option<&'dm K>, &'dm mut V);
//     fn next(&'dm mut self) -> Option<Self::Item> {
//         // if let Some(v) = self.dm.vec.get(self.idx) {
//         if self.dm.vec.get(self.idx).is_some() {
//             self.idx += 1;
//             self.dm.get_mut_with_key(self.idx -1)
//         } else {
//             None
//         }
//     }
// }

/* impl From */

impl<K: Hash + Eq, V, const N: usize> From<[V; N]> for DeqMap<K, V> {
    /// Converts an array of values `[V; N]` into a `DeqMap<_, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// assert_eq![DeqMap::<&str, _>::from([1, 2, 3, 4]), [1, 2, 3, 4].into()];
    /// ```
    fn from(arr: [V; N]) -> Self {
        DeqMap::from_array(arr)
    }
}
impl<K: Hash + Eq, V, const N: usize> From<[(K, V); N]> for DeqMap<K, V> {
    /// Converts an array of values `[V; N]` into a `DeqMap<_, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm1 = DeqMap::<&str, i32>::from([("a", 1), ("b", 2)]);
    /// let dm2 = [("a", 1), ("b", 2)].into();
    /// assert_eq![dm1, dm2];
    /// ```
    fn from(arr: [(K, V); N]) -> Self {
        DeqMap::from_keyed_array(arr)
    }
}

impl<K: Hash + Eq, V> From<Vec<V>> for DeqMap<K, V> {
    /// Converts a vec of values `Vec<V>` into a `DeqMap<_, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// assert_eq![DeqMap::<&str, _>::from(vec![1, 2, 3, 4]), vec![1, 2, 3, 4].into()];
    /// ```
    fn from(vec: Vec<V>) -> Self {
        DeqMap::from_vec(vec)
    }
}

impl<K: Hash + Eq, V> From<Vec<(K, V)>> for DeqMap<K, V> {
    /// Converts a vec of keys and values `Vec<K, V>` into a `DeqMap<K, V>`.
    ///
    /// # Examples
    /// ```
    /// use deqmap::DeqMap;
    ///
    /// let dm1 = DeqMap::<&str, i32>::from(vec![("a", 1), ("b", 2)]);
    /// let dm2 = vec![("a", 1), ("b", 2)].into();
    /// assert_eq![dm1, dm2];
    /// ```
    fn from(vec: Vec<(K, V)>) -> Self {
        DeqMap::from_keyed_vec(vec)
    }
}
