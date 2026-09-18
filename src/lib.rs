mod hash_set_intern;
#[cfg(feature = "roaring")]
mod roaring_intern;

pub use hash_set_intern::{I32HashSet, II32HashSet, IU32HashSet, U32HashSet};
use hashbrown::{HashTable, hash_table::Entry};
use parking_lot::RwLock;
#[cfg(feature = "roaring")]
pub use roaring_intern::{HashableRoaringBitmap, IRoaringBitmap};
use rustc_hash::FxHasher;
use std::{
    borrow::{Borrow, Cow},
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
    ops::Deref,
    sync::Arc,
};

/// Types that can be interned for memory-efficient deduplication.
///
/// Implementing this trait allows values to be converted into `Interned<T>`,
/// which guarantees pointer equality for identical values — ideal for strings,
/// symbols, or any frequently-repeated data.
///
/// # Requirements
/// - `Eq`, `Hash`: Values must be comparable and hashable.
/// - `'static`: Must not contain non-static references.
///
/// # Example
/// ```
/// use intern::{Internable, Interned, Interner};
///
/// #[derive(Eq, Hash, PartialEq)]
/// struct Symbol(&'static str);
///
/// impl Internable for Symbol {
///     fn interner() -> &'static Interner<Self> {
///         static INTERNER: Interner<Symbol> = Interner::new();
///         &INTERNER
///     }
/// }
///
/// let a = Interned::new(Symbol("hello"));
/// let b = Interned::new(Symbol("hello"));
/// assert!(a.ptr_eq(&b)); // Same underlying Arc!
/// ```
pub trait Internable: Eq + Hash + 'static {
    /// The global interner used to deduplicate instances of this type.
    fn interner() -> &'static Interner<Self>;
}

impl Internable for str {
    #[inline]
    fn interner() -> &'static Interner<Self> {
        static INTERNER: Interner<str> = Interner::new();
        &INTERNER
    }
}

/// An interned value with pointer identity semantics.
///
/// Two `Interned<T>` values are equal *only if* they point to the same `Arc<T>`.
/// This enables fast comparisons and automatic deduplication across the app.
///
/// # Memory Safety
/// Interned values are automatically removed from the interner when no longer referenced,
/// preventing leaks while allowing reuse of common values.
///
/// # Example
/// ```
/// use intern::Interned;
///
/// let a = Interned::from("hello");
/// let b = Interned::from("hello".to_string());
/// assert!(a.ptr_eq(&b)); // true
/// ```
pub struct Interned<T: Internable + ?Sized>(Arc<T>);

impl<T: Internable + ?Sized> Interned<T> {
    #[inline]
    pub fn new(value: T) -> Self
    where
        T: Sized,
    {
        T::interner().intern(value, Arc::new)
    }

    #[inline]
    pub fn as_inner(&self) -> &T {
        &self.0
    }

    /// Returns `true` if both values point to the same underlying `Arc<T>`.
    ///
    /// Faster than `==` since it compares pointers directly — ideal for hot paths.
    ///
    /// # Use Case
    /// Useful in ASTs, symbol tables, or any scenario where you care about *identity*, not value.
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<T: Internable + ?Sized> AsRef<T> for Interned<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Internable + ?Sized> Borrow<T> for Interned<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl<T: Internable + ?Sized> Clone for Interned<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Debug + Internable + ?Sized> Debug for Interned<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T: Default + Internable> Default for Interned<T> {
    #[inline]
    fn default() -> Self {
        Self::from(T::default())
    }
}

impl<T: Internable + ?Sized> Deref for Interned<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Internable + ?Sized> Drop for Interned<T> {
    #[inline]
    fn drop(&mut self) {
        // Fast path: someone else still holds a handle, nothing to clean up.
        if Arc::strong_count(&self.0) == 2 {
            T::interner().remove_if_unreferenced(&self.0);
        }
    }
}

impl<T: Display + Internable + ?Sized> Display for Interned<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&**self, f)
    }
}

impl<T: Internable + ?Sized> Eq for Interned<T> {}

impl<T: Internable> From<T> for Interned<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T: Internable + ?Sized> From<Box<T>> for Interned<T> {
    #[inline]
    fn from(value: Box<T>) -> Self {
        T::interner().intern(value, Arc::from)
    }
}

impl<'a, T> From<Cow<'a, T>> for Interned<T>
where
    T: Internable + ToOwned + ?Sized,
    Interned<T>: From<&'a T> + From<T::Owned>,
{
    #[inline]
    fn from(value: Cow<'a, T>) -> Self {
        match value {
            Cow::Borrowed(s) => Self::from(s),
            Cow::Owned(s) => Self::from(s),
        }
    }
}

impl From<&str> for Interned<str> {
    #[inline]
    fn from(value: &str) -> Self {
        str::interner().intern(value, Arc::from)
    }
}

impl From<String> for Interned<str> {
    #[inline]
    fn from(value: String) -> Self {
        str::interner().intern(value, Arc::from)
    }
}

impl<T: Internable + ?Sized> Hash for Interned<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

impl<T: Internable + ?Sized> PartialEq for Interned<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<T: Internable + ?Sized> PartialEq<T> for Interned<T> {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        *self.0 == *other
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for Interned<T>
where
    T: ?Sized + Internable + ToOwned,
    for<'a> Cow<'a, T>: serde::Deserialize<'de>,
    Interned<T>: From<Cow<'de, T>>,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Cow::<'de, T>::deserialize(deserializer).map(Interned::from)
    }
}

#[cfg(feature = "serde")]
impl<T> serde::Serialize for Interned<T>
where
    T: serde::Serialize + Internable + ?Sized,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

const SHARD_BITS: u32 = 6;
const SHARDS: usize = 1 << SHARD_BITS;

/// One shard per cache line so neighbouring shards don't ping-pong under contention.
#[repr(align(64))]
struct Shard<T: ?Sized>(RwLock<HashTable<Arc<T>>>);

/// A thread-safe interner that deduplicates values of type `T`.
///
/// Stores `Arc<T>` entries and returns `Interned<T>` handles with guaranteed
/// pointer identity for equal values. Automatically cleans up unused entries.
///
/// # Performance
/// - O(1) insert/lookup using `FxHasher`.
/// - Sharded; lookups of already-interned values only take a shared (read) lock.
/// - Automatic garbage collection on drop.
///
/// # Example
/// ```
/// use intern::Interned;
/// let a = Interned::from("hello");
/// let b = Interned::from("hello");
/// assert!(a.ptr_eq(&b));
/// ```
pub struct Interner<T: ?Sized + Internable> {
    shards: [Shard<T>; SHARDS],
}

impl<T: ?Sized + Internable> Interner<T> {
    /// Creates a new, empty interner.
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self {
            shards: [const { Shard(RwLock::new(HashTable::new())) }; SHARDS],
        }
    }

    /// Interns `value`, building the `Arc` with `make` only when it is not already present.
    ///
    /// `V: Borrow<T>` lets owned (`String`, `Box<T>`, `T`) and borrowed (`&str`, `&T`)
    /// inputs share one implementation without an up-front allocation or clone.
    #[inline]
    fn intern<V: Borrow<T>>(&self, value: V, make: impl FnOnce(V) -> Arc<T>) -> Interned<T> {
        let (shard, hash) = self.locate(value.borrow());

        {
            let table = shard.read();
            if let Some(arc) = table.find(hash, |arc| **arc == *value.borrow()) {
                return Interned(arc.clone());
            }
        }

        let mut table = shard.write();
        match table.entry(hash, |arc| **arc == *value.borrow(), rehash) {
            Entry::Occupied(e) => Interned(e.get().clone()),
            Entry::Vacant(e) => Interned(e.insert(make(value)).get().clone()),
        }
    }

    /// Removes `arc` from the interner if the caller's handle is the last one outside the map.
    fn remove_if_unreferenced(&self, arc: &Arc<T>) {
        let (shard, hash) = self.locate(arc);
        let mut table = shard.write();

        // Re-check under the lock: another thread may have interned the same value
        // (bumping the count) between the caller's check and our acquiring the lock.
        // At exactly 2 the only owners are the dropping handle and the map itself.
        if Arc::strong_count(arc) == 2
            && let Ok(e) = table.find_entry(hash, |v| Arc::ptr_eq(v, arc))
        {
            e.remove();
        }
    }

    #[inline]
    fn locate(&self, value: &T) -> (&RwLock<HashTable<Arc<T>>>, u64) {
        let hash = hash_val(value);
        let shard = &self.shards[(hash as usize) & (SHARDS - 1)].0;
        (shard, hash >> SHARD_BITS)
    }

    /// Returns the number of distinct values currently interned.
    ///
    /// Only includes values still referenced by at least one `Interned<T>`.
    /// Takes a read lock on every shard, so avoid calling it on hot paths.
    ///
    /// # Example
    /// ```
    /// use intern::{Interned, Internable};
    ///
    /// let interner = <str as Internable>::interner();
    ///
    /// assert_eq!(interner.len(), 0);
    /// let _x = Interned::from("a");
    /// assert_eq!(interner.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.shards.iter().map(|s| s.0.read().len()).sum()
    }

    /// Returns `true` if no values are currently interned.
    ///
    /// Equivalent to `len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.0.read().is_empty())
    }
}

/// Hash for the table itself: the low `SHARD_BITS` are already spent selecting the shard,
/// so they are dropped to keep bucket indices uniformly distributed within a shard.
#[inline]
fn rehash<T: Internable + ?Sized>(arc: &Arc<T>) -> u64 {
    hash_val(&**arc) >> SHARD_BITS
}

#[inline]
fn hash_val<T: Hash + ?Sized>(value: &T) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplication() {
        let a = Interned::from("hello");
        let b = Interned::from("hello");
        let c = Interned::from("world");

        assert!(a.ptr_eq(&b));
        assert!(!a.ptr_eq(&c));
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn deref_and_eq() {
        let s = Interned::from("rust");
        assert_eq!(s.as_inner(), &*Interned::from("rust"));
        assert_eq!(s, Interned::from("rust"));
    }

    #[test]
    fn len_and_is_empty() {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        struct Sym(&'static str);

        impl Internable for Sym {
            fn interner() -> &'static Interner<Self> {
                static SYM_INTERNER: Interner<Sym> = Interner::new();
                &SYM_INTERNER
            }
        }

        let interner = Sym::interner();
        assert!(interner.is_empty());
        let _a = Interned::new(Sym("a"));
        assert_eq!(interner.len(), 1);
        let _b = Interned::new(Sym("b"));
        assert_eq!(interner.len(), 2);
        drop(_a);
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn concurrent_intern() {
        use std::thread;

        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        struct Sym(&'static str);

        impl Internable for Sym {
            fn interner() -> &'static Interner<Self> {
                static SYM_INTERNER: Interner<Sym> = Interner::new();
                &SYM_INTERNER
            }
        }

        let handles: Vec<_> = (0..100)
            .map(|i| {
                thread::spawn(move || Interned::new(Sym(if i % 2 == 0 { "even" } else { "odd" })))
            })
            .collect();

        let mut evens = 0;
        let mut odds = 0;
        for h in handles {
            let sym = h.join().unwrap();
            if sym.as_inner() == &Sym("even") {
                evens += 1;
            } else {
                odds += 1;
            }
        }
        assert_eq!(evens, 50);
        assert_eq!(odds, 50);
    }

    #[test]
    fn hash_and_pointer_identity() {
        use std::collections::hash_map::DefaultHasher;
        let a = Interned::from("key");
        let b = a.clone();
        let c = Interned::from("key");

        assert_eq!(a, b);
        assert_eq!(a, c);

        // hash equality via pointer identity
        let mut h1 = DefaultHasher::new();
        let mut h2 = DefaultHasher::new();
        a.hash(&mut h1);
        c.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde_interned_str_compiles() {
        use serde::Deserialize;

        // This ensures `Interned<str>` implements Deserialize — if not, this won't compile.
        fn ensure_deserialize<T: for<'de> Deserialize<'de>>() {}

        ensure_deserialize::<Interned<str>>();
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde_interned_str_serialize_compiles() {
        use serde::Serialize;

        // Ensure Interned<str> implements Serialize — if not, this won't compile.
        fn ensure_serialize<T: Serialize>() {}
        ensure_serialize::<Interned<str>>();
    }
}
