/// # Examples
///
/// ```
/// use std::collections::hash_map::DefaultHasher;
/// use std::hash::{Hash, Hasher};
/// use intern::{IRoaringBitmap, Interned};
///
/// let rb1 = IRoaringBitmap::from_iter([1, 2, 3]);
/// let rb2 = IRoaringBitmap::from_iter([1, 2, 3]);
/// let rb3 = IRoaringBitmap::from_iter([4, 5]);
///
/// // identical content ⇒ same hash
/// assert_eq!(hash(&rb1), hash(&rb2));
/// assert_ne!(hash(&rb1), hash(&rb3));
///
/// // interning deduplicates
/// let a: Interned<_> = rb1.into();
/// let b: Interned<_> = rb2.into();
/// assert!(a.ptr_eq(&b));
///
/// // hashing is deterministic (no caching)
/// let mut h1 = DefaultHasher::new();
/// let mut h2 = DefaultHasher::new();
/// a.hash(&mut h1);
/// b.hash(&mut h2);
/// assert_eq!(h1.finish(), h2.finish());
///
/// fn hash<H: Hash>(h: &H) -> u64 {
///     let mut hasher = DefaultHasher::new();
///     h.hash(&mut hasher);
///     hasher.finish()
/// }
/// ```
use super::{Internable, Interned, Interner};
use roaring::RoaringBitmap;
use std::{
    hash::{Hash, Hasher},
    sync::Arc,
};

/// An Interned RoaringBitmap.
pub type IRoaringBitmap = Interned<HashableRoaringBitmap>;

/// A wrapper around `RoaringBitmap` that implements `Hash` and `Eq`
/// based on content, enabling interning — using fast FxHash and iteration.
/// Hash is computed on every call — no caching, no OnceLock.
#[derive(Clone, Debug, Default, PartialEq)]
#[repr(transparent)]
pub struct HashableRoaringBitmap(RoaringBitmap);

impl HashableRoaringBitmap {
    #[inline]
    fn from_bitmap_ref(b: &RoaringBitmap) -> &Self {
        // safety: HashableRoaringBitmap is #[repr(transparent)] around RoaringBitmap
        unsafe { &*(b as *const RoaringBitmap as *const HashableRoaringBitmap) }
    }

    /// Access the inner `RoaringBitmap`.
    #[inline]
    pub fn inner(&self) -> &RoaringBitmap {
        &self.0
    }

    /// Consume and return the inner `RoaringBitmap`.
    #[inline]
    pub fn into_inner(self) -> RoaringBitmap {
        self.0
    }
}

impl Eq for HashableRoaringBitmap {}

impl Hash for HashableRoaringBitmap {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);

        for val in self.0.iter() {
            val.hash(state);
        }
    }
}

impl Internable for HashableRoaringBitmap {
    #[inline]
    fn interner() -> &'static Interner<Self> {
        static INTERNER: Interner<HashableRoaringBitmap> = Interner::new();
        &INTERNER
    }
}

impl Interned<HashableRoaringBitmap> {
    #[inline]
    pub fn as_bitmap(&self) -> &RoaringBitmap {
        &self.0.0
    }
}

impl From<RoaringBitmap> for Interned<HashableRoaringBitmap> {
    #[inline]
    fn from(bitmap: RoaringBitmap) -> Self {
        HashableRoaringBitmap::interner().intern(HashableRoaringBitmap(bitmap), |mut v| {
            v.0.optimize();
            Arc::new(v)
        })
    }
}

impl From<&RoaringBitmap> for Interned<HashableRoaringBitmap> {
    #[inline]
    fn from(bitmap: &RoaringBitmap) -> Self {
        HashableRoaringBitmap::interner().intern(
            HashableRoaringBitmap::from_bitmap_ref(bitmap),
            |v| {
                let mut v = v.clone();
                v.0.optimize();
                Arc::new(v)
            },
        )
    }
}

impl From<Interned<HashableRoaringBitmap>> for RoaringBitmap {
    #[inline]
    fn from(v: Interned<HashableRoaringBitmap>) -> Self {
        v.0.0.clone()
    }
}

impl<'a> From<&'a Interned<HashableRoaringBitmap>> for &'a RoaringBitmap {
    #[inline]
    fn from(v: &'a Interned<HashableRoaringBitmap>) -> Self {
        &v.0.0
    }
}

/// Create a `HashableRoaringBitmap` from any iterator of `u32`.
///
/// # Example
/// ```
/// use intern::IRoaringBitmap;
/// let rb = IRoaringBitmap::from_iter([1, 2, 3]);
/// assert_eq!(rb.inner().len(), 3);
/// ```
impl FromIterator<u32> for Interned<HashableRoaringBitmap> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = u32>>(iter: I) -> Self {
        Self::from(RoaringBitmap::from_iter(iter))
    }
}

impl PartialEq<RoaringBitmap> for Interned<HashableRoaringBitmap> {
    #[inline]
    fn eq(&self, other: &RoaringBitmap) -> bool {
        &self.0.0 == other
    }
}

impl PartialEq<Interned<HashableRoaringBitmap>> for RoaringBitmap {
    #[inline]
    fn eq(&self, other: &Interned<HashableRoaringBitmap>) -> bool {
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
        let rb = IRoaringBitmap::from_iter(0..1_000);
        let mut h1 = DefaultHasher::new();
        let mut h2 = DefaultHasher::new();
        rb.hash(&mut h1);
        rb.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
    }

    #[test]
    fn intern_dedup() {
        let a = IRoaringBitmap::from_iter(1..10);
        let b = IRoaringBitmap::from_iter(1..10);
        assert!(a.ptr_eq(&b));
    }
}
