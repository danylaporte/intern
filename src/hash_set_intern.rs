use super::{Internable, Interned, Interner, SHARDS, hash_val};
use hashbrown::hash_map::RawEntryMut;
use std::{
    collections::hash_set::HashSet,
    fmt::{self, Debug, Formatter},
    hash::{BuildHasher, Hash, Hasher, RandomState},
    ops::{Deref, DerefMut},
    sync::{Arc, atomic::Ordering::Relaxed},
};

pub type I32HashSet = HashableHashSet<i32, rustc_hash::FxBuildHasher>;
pub type II32HashSet = Interned<I32HashSet>;
pub type IU32HashSet = Interned<U32HashSet>;
pub type U32HashSet = HashableHashSet<u32, rustc_hash::FxBuildHasher>;

/// A wrapper around `RoaringBitmap` that implements `Hash` and `Eq`
/// based on content, enabling interning — using fast FxHash and iteration.
/// Hash is computed on every call — no caching, no OnceLock.
#[derive(Clone)]
#[repr(transparent)]
pub struct HashableHashSet<T, S = RandomState>(HashSet<T, S>);

impl<T: Eq + Hash, S: BuildHasher> HashableHashSet<T, S> {
    #[inline]
    fn from_hashset_ref(b: &HashSet<T, S>) -> &Self {
        // safety: HashableRoaringBitmap is #[repr(transparent)] around RoaringBitmap
        unsafe { &*(b as *const HashSet<T, S> as *const HashableHashSet<T, S>) }
    }

    /// Access the inner `HashSet`.
    #[inline]
    pub fn inner(&self) -> &HashSet<T, S> {
        &self.0
    }

    /// Consume and return the inner `HashSet`.
    #[inline]
    pub fn into_inner(self) -> HashSet<T, S> {
        self.0
    }
}

impl<T: Debug + Eq + Hash, S: BuildHasher> Debug for HashableHashSet<T, S> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<T, S: Default> Default for HashableHashSet<T, S> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T, S> Deref for HashableHashSet<T, S> {
    type Target = HashSet<T, S>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, S> DerefMut for HashableHashSet<T, S> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Eq + Hash, S: BuildHasher> PartialEq for HashableHashSet<T, S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Eq + Hash, S: BuildHasher> Eq for HashableHashSet<T, S> {}

impl<T: Eq + Hash, S: BuildHasher> Hash for HashableHashSet<T, S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);

        for val in self.0.iter() {
            val.hash(state);
        }
    }
}

impl Internable for U32HashSet {
    #[inline]
    fn interner() -> &'static Interner<Self> {
        static INTERNER: Interner<U32HashSet> = Interner::new();
        &INTERNER
    }
}

impl<T, S> Interned<HashableHashSet<T, S>>
where
    HashableHashSet<T, S>: Internable,
{
    #[inline]
    pub fn as_set(&self) -> &HashSet<T, S> {
        &self.0.0
    }
}

impl<T, S> From<HashSet<T, S>> for Interned<HashableHashSet<T, S>>
where
    HashableHashSet<T, S>: Internable,
    S: BuildHasher,
    T: Eq + Hash,
{
    #[inline]
    fn from(set: HashSet<T, S>) -> Self {
        let interner = HashableHashSet::interner();
        let value = HashableHashSet(set);
        let hash = hash_val(&value);
        let idx = (hash as usize) & (SHARDS - 1);
        let mut shard = interner.shards[idx].lock();

        match shard.raw_entry_mut().from_hash(hash, |v| **v == value) {
            RawEntryMut::Occupied(e) => Interned(e.key().clone()),
            RawEntryMut::Vacant(e) => {
                let key = Arc::new(value);

                e.insert_hashed_nocheck(hash, key.clone(), ());
                interner.len.fetch_add(1, Relaxed);
                Interned(key)
            }
        }
    }
}

impl<T, S> From<&HashSet<T, S>> for Interned<HashableHashSet<T, S>>
where
    HashableHashSet<T, S>: Internable,
    S: BuildHasher + Clone,
    T: Clone + Eq + Hash,
{
    fn from(set: &HashSet<T, S>) -> Self {
        let interner = HashableHashSet::interner();
        let value = HashableHashSet::from_hashset_ref(set);
        let hash = hash_val(&value);
        let idx = (hash as usize) & (SHARDS - 1);
        let mut shard = interner.shards[idx].lock();

        match shard.raw_entry_mut().from_hash(hash, |v| **v == *value) {
            RawEntryMut::Occupied(e) => Interned(e.key().clone()),
            RawEntryMut::Vacant(e) => {
                let key = Arc::new(value.clone());

                e.insert_hashed_nocheck(hash, key.clone(), ());
                interner.len.fetch_add(1, Relaxed);
                Interned(key)
            }
        }
    }
}

impl<T, S> From<Interned<HashableHashSet<T, S>>> for HashSet<T, S>
where
    HashableHashSet<T, S>: Internable,
    S: Clone,
    T: Clone,
{
    #[inline]
    fn from(v: Interned<HashableHashSet<T, S>>) -> Self {
        v.0.0.clone()
    }
}

impl<'a, T, S> From<&'a Interned<HashableHashSet<T, S>>> for &'a HashSet<T, S>
where
    HashableHashSet<T, S>: Internable,
{
    #[inline]
    fn from(v: &'a Interned<HashableHashSet<T, S>>) -> Self {
        &v.0.0
    }
}

/// Create a `HashableRoaringBitmap` from any iterator of `u32`.
///
/// # Example
/// ```
/// use intern::IU32HashSet;
/// let rb = IU32HashSet::from_iter([1, 2, 3]);
/// assert_eq!(rb.inner().len(), 3);
/// ```
impl<T, S> FromIterator<T> for Interned<HashableHashSet<T, S>>
where
    HashableHashSet<T, S>: Internable,
    S: BuildHasher + Default,
    T: Eq + Hash,
{
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from(HashSet::from_iter(iter))
    }
}

impl<T, S> PartialEq<HashSet<T, S>> for Interned<HashableHashSet<T, S>>
where
    HashableHashSet<T, S>: Internable,
    S: BuildHasher,
    T: Eq + Hash,
{
    #[inline]
    fn eq(&self, other: &HashSet<T, S>) -> bool {
        &self.0.0 == other
    }
}

impl<T, S> PartialEq<Interned<HashableHashSet<T, S>>> for HashSet<T, S>
where
    HashableHashSet<T, S>: Internable,
    S: BuildHasher,
    T: Eq + Hash,
{
    #[inline]
    fn eq(&self, other: &Interned<HashableHashSet<T, S>>) -> bool {
        self == &other.0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[test]
    fn hash_deterministic() {
        let rb = IU32HashSet::from_iter(0..1_000);
        let mut h1 = DefaultHasher::new();
        let mut h2 = DefaultHasher::new();
        rb.hash(&mut h1);
        rb.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
    }

    #[test]
    fn intern_dedup() {
        let a = IU32HashSet::from_iter(1..10);
        let b = IU32HashSet::from_iter(1..10);
        assert!(a.ptr_eq(&b));
    }

    #[test]
    fn test_default_compiles() {
        let _ = IU32HashSet::default();
    }
}
