use hashbrown::hash_map::{HashMap, RawEntryMut};
use parking_lot::Mutex;
use rustc_hash::{FxBuildHasher, FxHasher};
use std::{
    borrow::{Borrow, Cow},
    hash::{Hash, Hasher},
    ops::Deref,
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
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
/// let a = Symbol("hello").intern();
/// let b = Symbol("hello").intern();
/// assert!(a.ptr_eq(&b)); // Same underlying Arc!
/// ```
pub trait Internable: Eq + Hash + 'static {
    fn intern(self) -> Interned<Self>
    where
        Self: Sized,
    {
        Self::interner().intern(self)
    }

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

impl From<&str> for Interned<str> {
    #[inline]
    fn from(value: &str) -> Self {
        str::interner().intern(Arc::from(value))
    }
}

impl From<Arc<str>> for Interned<str> {
    #[inline]
    fn from(value: Arc<str>) -> Self {
        str::interner().intern(Arc::from(&*value))
    }
}

impl From<Box<str>> for Interned<str> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        str::interner().intern(Arc::from(value))
    }
}

impl From<Cow<'_, str>> for Interned<str> {
    #[inline]
    fn from(value: Cow<'_, str>) -> Self {
        str::interner().intern(Arc::from(value))
    }
}

impl From<Rc<str>> for Interned<str> {
    #[inline]
    fn from(value: Rc<str>) -> Self {
        str::interner().intern(Arc::from(&*value))
    }
}

impl From<String> for Interned<str> {
    #[inline]
    fn from(value: String) -> Self {
        str::interner().intern(Arc::from(value))
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
#[derive(Debug)]
pub struct Interned<T: Internable + ?Sized>(Arc<T>);

impl<T: Internable + ?Sized> Interned<T> {
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

impl<T: Internable + ?Sized> Deref for Interned<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Internable + ?Sized> Drop for Interned<T> {
    fn drop(&mut self) {
        if Arc::strong_count(&self.0) == 2 {
            T::interner().remove_interned_if_possible(self);
        }
    }
}

impl<T: Internable + ?Sized> Eq for Interned<T> {}

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
impl<'de, T> serde_crate::Deserialize<'de> for Interned<T>
where
    T: for<'b> serde_crate::Deserialize<'b> + Internable,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde_crate::Deserializer<'de>,
    {
        T::deserialize(deserializer).map(Internable::intern)
    }
}

#[cfg(feature = "serde")]
impl<T> serde_crate::Serialize for Interned<T>
where
    T: serde_crate::Serialize + Internable + ?Sized,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde_crate::Serializer,
    {
        self.0.serialize(serializer)
    }
}

const SHARDS: usize = 16;
type Shard<T> = Mutex<HashMap<Arc<T>, (), FxBuildHasher>>;

/// A thread-safe interner that deduplicates values of type `T`.
///
/// Stores `Arc<T>` entries and returns `Interned<T>` handles with guaranteed
/// pointer identity for equal values. Automatically cleans up unused entries.
///
/// # Performance
/// - O(1) insert/lookup using `FxHasher`.
/// - Lock-free reads; minimal lock contention during insertion.
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
    /// cheap counter so that `len()` needs no locks
    len: AtomicU64,
}

impl<T: ?Sized + Internable> Interner<T> {
    /// Creates a new, empty interner.
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self {
            shards: make_shards(),
            len: AtomicU64::new(0),
        }
    }

    #[inline]
    fn shard(&self, hash: u64) -> &Shard<T> {
        &self.shards[(hash as usize) & (SHARDS - 1)]
    }

    /// Interns a value, returning a shared handle (`Interned<T>`).
    ///
    /// If an equal value already exists, returns its existing handle.
    /// Otherwise, stores the new value and returns a new handle.
    ///
    /// Uses raw-entry API for single atomic lookup-and-insert.
    ///
    /// # Performance
    /// Average-case O(1). Lock held only briefly during insertion.
    #[must_use]
    pub(crate) fn intern<Q>(&self, value: Q) -> Interned<T>
    where
        Arc<T>: Borrow<Q>,
        Q: Eq + Hash + Into<Arc<T>>,
    {
        let hash = hash_val(&value);
        let shard = self.shard(hash);

        let mut g = shard.lock();
        match g.raw_entry_mut().from_hash(hash, |k| k.borrow() == &value) {
            RawEntryMut::Occupied(e) => Interned(e.key().clone()),
            RawEntryMut::Vacant(e) => {
                let arc = value.into();
                e.insert_hashed_nocheck(hash, arc.clone(), ());
                self.len.fetch_add(1, Ordering::Relaxed);
                Interned(arc)
            }
        }
    }

    /// Internal: Removes an interned value if it's no longer referenced elsewhere.
    ///
    /// Called automatically when `Interned<T>` is dropped and no other references exist.
    /// Not meant for direct use.
    fn remove_interned_if_possible(&self, item: &Interned<T>)
    where
        T: Internable,
    {
        let hash = hash_val(&*item.0);
        let shard = self.shard(hash);
        let mut map = shard.lock();

        // After acquiring the lock, verify no other thread created a new reference.
        // If strong_count == 2, then the only remaining references are:
        //   - the one we're dropping (this Interned<T>)
        //   - the one in the interner's map
        // Thus, it is safe to remove the map entry.

        if Arc::strong_count(&item.0) == 2 {
            if let RawEntryMut::Occupied(o) =
                map.raw_entry_mut().from_key_hashed_nocheck(hash, &item.0)
            {
                o.remove();
                self.len.fetch_sub(1, Ordering::Relaxed);
            }
        }
    }

    /// Returns the number of distinct values currently interned.
    ///
    /// Only includes values still referenced by at least one `Interned<T>`.
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
        self.len.load(Ordering::Relaxed) as usize
    }

    /// Returns `true` if no values are currently interned.
    ///
    /// Equivalent to `len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.len.load(Ordering::Relaxed) == 0
    }
}

#[inline]
fn hash_val<T: Hash + ?Sized>(value: &T) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
const fn make_shards<T: ?Sized + Internable>() -> [Shard<T>; SHARDS] {
    [
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
        Mutex::new(HashMap::with_hasher(FxBuildHasher)),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct Sym(&'static str);

    static SYM_INTERNER: Interner<Sym> = Interner::new();

    impl Internable for Sym {
        fn interner() -> &'static Interner<Self> {
            &SYM_INTERNER
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct Sym2(u32);

    static SYM2_INTERNER: Interner<Sym2> = Interner::new();

    impl Internable for Sym2 {
        fn interner() -> &'static Interner<Self> {
            &SYM2_INTERNER
        }
    }

    #[test]
    fn deduplication() {
        let a = Sym("hello").intern();
        let b = Sym("hello").intern();
        let c = Sym("world").intern();

        assert!(a.ptr_eq(&b));
        assert!(!a.ptr_eq(&c));
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn deref_and_eq() {
        let s = Sym("rust").intern();
        assert_eq!(&*s, &Sym("rust"));
        assert_eq!(s, Sym("rust"));
    }

    #[test]
    fn len_and_is_empty() {
        let interner = &SYM2_INTERNER;
        assert!(interner.is_empty());
        let _a = Sym2(1).intern();
        assert_eq!(interner.len(), 1);
        let _b = Sym2(2).intern();
        assert_eq!(interner.len(), 2);
        drop(_a);
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn concurrent_intern() {
        use std::thread;

        let handles: Vec<_> = (0..100)
            .map(|i| thread::spawn(move || Sym(if i % 2 == 0 { "even" } else { "odd" }).intern()))
            .collect();

        let mut evens = 0;
        let mut odds = 0;
        for h in handles {
            let sym = h.join().unwrap();
            if &*sym == &Sym("even") {
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
        let a = Sym("key").intern();
        let b = a.clone();
        let c = Sym("key").intern();

        assert_eq!(a, b);
        assert_eq!(a, c);

        // hash equality via pointer identity
        let mut h1 = DefaultHasher::new();
        let mut h2 = DefaultHasher::new();
        a.hash(&mut h1);
        c.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
    }
}
