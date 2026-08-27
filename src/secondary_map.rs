//! Small extraction-local interning and secondary-map helpers.
//!
//! `InternerBuilder`/`Interner` follow the two-phase shape used by interning
//! crates such as `lasso`: first intern keys into a growable builder, then
//! freeze it into a read-only interner. `SecondaryMap` follows `slotmap`'s
//! terminology: the key universe is owned elsewhere, and the secondary
//! structure stores associated data for those keys.
//!
//! This stays local because greedy-DAG extraction needs a narrow combination:
//! dense never-deleted ids, sparse iteration, bitset membership, and a cached
//! monoid aggregate. `slotmap` provides generational deletion safety we do not
//! need and its `SparseSecondaryMap` is `HashMap`-backed; `rustc_index` and
//! `index_vec` cover dense typed indexing, but not sparse associated payloads
//! with an aggregate. `indexmap::IndexSet` (already in the tree, via core's
//! `TermDag`) does cover the interner half, and swapping it in measures the
//! same on the Taylor greedy-DAG canary. It is not used because it would
//! replace only that half: the id-indexed structures here are the point.
//! `SecondaryMap` indexes a `Vec` directly and `SecondarySet` a bitset, both
//! without hashing at all, and `AggregatedSparseSecondaryMap` maintains a
//! running monoid total on insert so cost comparison never re-sums or
//! subtracts. See:
//! <https://docs.rs/lasso/latest/lasso/trait.IntoReader.html>,
//! <https://docs.rs/slotmap/latest/slotmap/struct.SparseSecondaryMap.html>,
//! <https://docs.rs/indexmap/latest/indexmap/set/struct.IndexSet.html> and
//! <https://doc.rust-lang.org/beta/nightly-rustc/rustc_index/vec/struct.IndexVec.html>.

use egglog::extract::MonoidCost;
use fixedbitset::FixedBitSet;
use hashbrown::{Equivalent, HashMap};
use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

/// Dense id allocated by an [`InternerBuilder`].
///
/// The key type defines the id-space. An `InternerBuilder<String>` produces
/// `InternId<String>`, while an `InternerBuilder<DagCostKey>` produces
/// `InternId<DagCostKey>`. If two interners have the same key type but must
/// not share ids, wrap one key in a newtype. This is the same type-level
/// protection provided by typed-index APIs, scoped to this module's interner.
pub(super) struct InternId<K> {
    index: usize,
    // This is a typed integer handle, not storage for `K`. `fn() -> K` keeps
    // the marker covariant in `K` without making auto traits behave as if this
    // id owns a `K`; see the Rustonomicon's `PhantomData` table:
    // https://doc.rust-lang.org/nomicon/phantom-data.html#table-of-phantomdata-patterns
    // and the standard docs:
    // https://doc.rust-lang.org/std/marker/struct.PhantomData.html
    _key: PhantomData<fn() -> K>,
}

impl<K> Clone for InternId<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for InternId<K> {}

impl<K> fmt::Debug for InternId<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("InternId").field(&self.index).finish()
    }
}

impl<K> PartialEq for InternId<K> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<K> Eq for InternId<K> {}

impl<K> Hash for InternId<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

/// Growable interner for building one dense id-space.
///
/// Use this while discovering all reachable keys. Once discovery is complete,
/// call [`InternerBuilder::freeze`] to get an [`Interner`] that can construct
/// secondary maps and sets. Keeping construction on the frozen type makes the
/// fixed-universe requirement explicit in the API.
pub(super) struct InternerBuilder<K> {
    ids: HashMap<K, InternId<K>>,
}

impl<K> Default for InternerBuilder<K> {
    fn default() -> Self {
        Self {
            ids: HashMap::default(),
        }
    }
}

impl<K> InternerBuilder<K> {
    /// Freezes the key universe so secondary maps can be safely sized from it.
    #[inline]
    pub(super) fn freeze(self) -> Interner<K> {
        Interner { ids: self.ids }
    }
}

impl<K: Eq + Hash> InternerBuilder<K> {
    /// Returns the existing id for `key`, or allocates the next dense id.
    ///
    /// Interned ids stay stable after freezing. Keys are not removed because
    /// extraction builds one reachable universe per run.
    #[inline]
    pub(super) fn intern(&mut self, key: K) -> InternId<K> {
        if let Some(id) = self.ids.get(&key) {
            return *id;
        }

        let id = InternId {
            index: self.ids.len(),
            _key: PhantomData,
        };
        self.ids.insert(key, id);
        id
    }

    /// Looks up an already-interned key without allocating a new id.
    ///
    /// This lets discovery reuse existing ids without cloning keys such as sort
    /// names when no allocation is needed.
    #[inline]
    pub(super) fn get<Q>(&self, key: &Q) -> Option<InternId<K>>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.ids.get(key).copied()
    }
}

/// Frozen interner for one dense id-space.
///
/// This owns the final key universe for compatible secondary maps and sets.
/// Candidate-local maps do not borrow it, but callers construct them through
/// this type so the fixed id-space is explicit at call sites.
pub(super) struct Interner<K> {
    ids: HashMap<K, InternId<K>>,
}

impl<K> Interner<K> {
    /// Returns the number of unique keys in this dense id-space.
    #[inline]
    pub(super) fn len(&self) -> usize {
        self.ids.len()
    }

    /// Creates an aggregated sparse secondary map for this frozen id-space.
    ///
    /// The capacity is for expected present entries, not for the full interned
    /// universe. The membership bitset is sized from the frozen universe.
    #[inline]
    fn aggregated_map_with_capacity<V: MonoidCost>(
        &self,
        entries_capacity: usize,
    ) -> AggregatedSparseSecondaryMap<K, V> {
        AggregatedSparseSecondaryMap {
            entries: Vec::with_capacity(entries_capacity.min(self.len())),
            present: self.secondary_set(),
            total: V::identity(),
        }
    }

    /// Creates a dense secondary map for this frozen id-space.
    ///
    /// Use this for long-lived per-id state when lookup speed is more important
    /// than avoiding empty slots.
    #[inline]
    pub(super) fn secondary_map<V>(&self) -> SecondaryMap<K, V> {
        let mut values = Vec::with_capacity(self.len());
        values.resize_with(self.len(), || None);
        SecondaryMap {
            values,
            _key: PhantomData,
        }
    }

    /// Creates a dense secondary set for this frozen id-space.
    ///
    /// Use this when membership checks should be direct bitset operations
    /// instead of hash lookups.
    #[inline]
    pub(super) fn secondary_set(&self) -> SecondarySet<K> {
        SecondarySet {
            present: FixedBitSet::with_capacity(self.len()),
            _key: PhantomData,
        }
    }
}

impl<K: Eq + Hash> Interner<K> {
    /// Looks up an already-interned key.
    ///
    /// Frozen interners cannot allocate new ids; callers must have interned all
    /// reachable keys before calling [`InternerBuilder::freeze`].
    #[inline]
    pub(super) fn get<Q>(&self, key: &Q) -> Option<InternId<K>>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.ids.get(key).copied()
    }
}

/// Dense secondary set over a fixed interned id-space.
///
/// This is the set counterpart to [`SecondaryMap`]. It stores membership in a
/// bitset indexed directly by [`InternId`], so it is useful for hot temporary
/// sets once the id universe is fixed.
pub(super) struct SecondarySet<K> {
    present: FixedBitSet,
    // Same non-owning key-space marker as `InternId`.
    _key: PhantomData<fn() -> K>,
}

impl<K> Clone for SecondarySet<K> {
    fn clone(&self) -> Self {
        Self {
            present: self.present.clone(),
            _key: PhantomData,
        }
    }
}

impl<K> SecondarySet<K> {
    /// Returns whether `id` is present.
    #[inline]
    fn contains(&self, id: InternId<K>) -> bool {
        debug_assert!(id.index < self.present.len());
        self.present.contains(id.index)
    }

    /// Inserts `id` and returns whether it was absent.
    #[inline]
    pub(super) fn insert(&mut self, id: InternId<K>) -> bool {
        if self.contains(id) {
            false
        } else {
            self.present.insert(id.index);
            true
        }
    }

    /// Removes `id` from the set.
    #[inline]
    pub(super) fn remove(&mut self, id: InternId<K>) {
        debug_assert!(id.index < self.present.len());
        self.present.set(id.index, false);
    }
}

/// Dense secondary map over a fixed interned id-space.
///
/// This is the plain lookup counterpart to [`AggregatedSparseSecondaryMap`].
/// It stores one optional payload slot for each id allocated by an [`Interner`]
/// and uses the id index directly, avoiding hash lookups in fixed-point state.
/// Construct it after the interner has seen the full reachable universe.
pub(super) struct SecondaryMap<K, V> {
    values: Vec<Option<V>>,
    // Same non-owning key-space marker as `InternId`.
    _key: PhantomData<fn() -> K>,
}

impl<K, V> SecondaryMap<K, V> {
    /// Returns the payload for `id`, if one has been inserted.
    #[inline]
    pub(super) fn get(&self, id: InternId<K>) -> Option<&V> {
        debug_assert!(id.index < self.values.len());
        self.values.get(id.index).and_then(Option::as_ref)
    }

    /// Inserts or replaces the payload for `id`.
    #[inline]
    pub(super) fn insert(&mut self, id: InternId<K>, value: V) -> Option<V> {
        debug_assert!(id.index < self.values.len());
        self.values[id.index].replace(value)
    }
}

/// Sparse secondary map over a fixed dense id-space with a cached aggregate.
///
/// Construct this through [`Interner::aggregated_map_with_capacity`] so the
/// interner that allocated the ids also sizes the membership structure. This
/// behaves like a sparse insertion-ordered map from interned ids to payloads:
/// each id can be inserted once, membership tests are constant-time, iteration
/// visits only present entries, and the monoid total is cached on insert. Each
/// map uses one membership bit per interned key; replacing the bitset with
/// linear entry scans made the greedy-DAG benchmark roughly 65-70% slower (see
/// `.agents/logs/2026-06-24-greedy-dag-extractor-perf.md`).
pub(super) struct AggregatedSparseSecondaryMap<K, V: MonoidCost> {
    entries: Vec<(InternId<K>, V)>,
    present: SecondarySet<K>,
    total: V,
}

impl<K, V: MonoidCost> Clone for AggregatedSparseSecondaryMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            entries: self.entries.clone(),
            present: self.present.clone(),
            total: self.total.clone(),
        }
    }
}

impl<K, V: MonoidCost> AggregatedSparseSecondaryMap<K, V> {
    /// Unions several sparse secondary maps by cloning the largest input first.
    ///
    /// This is the efficient merge operation used by greedy-DAG candidate
    /// construction. It follows
    /// [extraction-gym's `faster-greedy-dag` strategy](https://github.com/egraphs-good/extraction-gym/blob/903ba0f818b50608fe20ae9e0f03c35cb27bc50a/src/extract/faster_greedy_dag.rs#L57-L62):
    /// start from the largest child set, then insert missing ids from smaller
    /// sets, so the largest set is not replayed entry by entry. Duplicate ids
    /// are counted once.
    ///
    /// `extra_capacity` reserves space for entries the caller will immediately
    /// add after the union. The interner is required because an empty union
    /// still needs the dense id-space size for later constant-time membership
    /// checks.
    #[inline]
    pub(super) fn union_by_cloning_largest<M>(
        interner: &Interner<K>,
        maps: &[M],
        extra_capacity: usize,
    ) -> Self
    where
        M: Borrow<AggregatedSparseSecondaryMap<K, V>>,
    {
        let mut entries_capacity = extra_capacity;
        let mut biggest: Option<(usize, usize)> = None;
        for (idx, map) in maps.iter().enumerate() {
            let map: &AggregatedSparseSecondaryMap<K, V> = map.borrow();
            let len = map.len();
            entries_capacity = entries_capacity.saturating_add(len);
            if biggest.is_none_or(|(_, biggest_len)| len > biggest_len) {
                biggest = Some((idx, len));
            }
        }
        let entries_capacity = entries_capacity.min(interner.len());

        let Some((biggest_idx, _)) = biggest else {
            return interner.aggregated_map_with_capacity(entries_capacity);
        };

        let biggest: &AggregatedSparseSecondaryMap<K, V> = maps[biggest_idx].borrow();
        let mut merged = biggest.clone();
        merged
            .entries
            .reserve(entries_capacity.saturating_sub(merged.len()));

        for (idx, map) in maps.iter().enumerate() {
            if idx != biggest_idx {
                let map: &AggregatedSparseSecondaryMap<K, V> = map.borrow();
                for (id, value) in &map.entries {
                    merged.insert_if_absent(*id, value.clone());
                }
            }
        }

        merged
    }

    /// Returns whether `id` already has a payload in this secondary map.
    #[inline]
    pub(super) fn contains(&self, id: InternId<K>) -> bool {
        self.present.contains(id)
    }

    /// Inserts `value` for `id` if the id is not already present.
    ///
    /// If `id` is already present, the existing payload wins and `value` is
    /// ignored. First inserts preserve sparse iteration order and update the
    /// cached aggregate without requiring subtraction.
    #[inline]
    pub(super) fn insert_if_absent(&mut self, id: InternId<K>, value: V) {
        if self.present.insert(id) {
            self.total = self.total.clone().combine(&value);
            self.entries.push((id, value));
        }
    }

    /// Returns the number of present id/payload pairs.
    #[inline]
    fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns the cached aggregate of all present payloads.
    ///
    /// For extraction costs, this avoids inspecting or subtracting arbitrary
    /// cost values while still making candidate comparisons cheap.
    #[inline]
    pub(super) fn total(&self) -> &V {
        &self.total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interner_reuses_existing_ids() {
        let mut builder = InternerBuilder::<String>::default();

        let first = builder.intern("a".to_owned());
        let second = builder.intern("b".to_owned());

        assert_eq!(builder.intern("a".to_owned()), first);
        assert_eq!(builder.get("a"), Some(first));
        let interner = builder.freeze();
        assert_eq!(interner.get("a"), Some(first));
        assert_eq!(interner.get("b"), Some(second));
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn secondary_set_tracks_membership_by_id() {
        let mut builder = InternerBuilder::<&'static str>::default();
        let a = builder.intern("a");
        let b = builder.intern("b");
        let interner = builder.freeze();
        let mut set = interner.secondary_set();

        assert!(set.insert(a));
        assert!(!set.insert(a));
        assert!(set.contains(a));
        assert!(!set.contains(b));

        set.remove(a);
        assert!(!set.contains(a));
    }

    #[test]
    fn secondary_map_stores_payloads_by_id() {
        let mut builder = InternerBuilder::<&'static str>::default();
        let a = builder.intern("a");
        let b = builder.intern("b");
        let interner = builder.freeze();
        let mut map = interner.secondary_map();

        assert_eq!(map.insert(a, 4), None);
        assert_eq!(map.insert(a, 10), Some(4));
        assert_eq!(map.get(a), Some(&10));
        assert_eq!(map.get(b), None);
    }

    #[test]
    fn aggregated_map_inserts_each_id_once_and_caches_total() {
        let mut builder = InternerBuilder::<&'static str>::default();
        let a = builder.intern("a");
        let b = builder.intern("b");
        let interner = builder.freeze();
        let mut map: AggregatedSparseSecondaryMap<&'static str, usize> =
            interner.aggregated_map_with_capacity(2);

        map.insert_if_absent(a, 4);
        map.insert_if_absent(a, 10);
        map.insert_if_absent(b, 3);

        assert!(map.contains(a));
        assert!(map.contains(b));
        assert_eq!(map.len(), 2);
        assert_eq!(map.entries, [(a, 4), (b, 3)]);
        assert_eq!(*map.total(), 7);
    }

    #[test]
    fn cloned_maps_keep_membership() {
        let mut builder = InternerBuilder::<&'static str>::default();
        let a = builder.intern("a");
        let b = builder.intern("b");
        let interner = builder.freeze();
        let mut map: AggregatedSparseSecondaryMap<&'static str, usize> =
            interner.aggregated_map_with_capacity(1);

        map.insert_if_absent(a, 1);
        let mut cloned = map.clone();
        cloned.insert_if_absent(b, 2);

        assert_eq!(map.entries, [(a, 1)]);
        assert_eq!(cloned.entries, [(a, 1), (b, 2)]);
        assert_eq!(*cloned.total(), 3);
    }

    #[test]
    fn union_by_cloning_largest_keeps_each_id_once() {
        let mut builder = InternerBuilder::<&'static str>::default();
        let a = builder.intern("a");
        let b = builder.intern("b");
        let c = builder.intern("c");
        let d = builder.intern("d");
        let interner = builder.freeze();
        let mut big: AggregatedSparseSecondaryMap<&'static str, usize> =
            interner.aggregated_map_with_capacity(3);
        let mut small: AggregatedSparseSecondaryMap<&'static str, usize> =
            interner.aggregated_map_with_capacity(2);

        big.insert_if_absent(a, 1);
        big.insert_if_absent(b, 2);
        big.insert_if_absent(c, 3);
        small.insert_if_absent(b, 2);
        small.insert_if_absent(d, 4);

        let union =
            AggregatedSparseSecondaryMap::union_by_cloning_largest(&interner, &[big, small], 0);

        assert!(union.contains(a));
        assert!(union.contains(b));
        assert!(union.contains(c));
        assert!(union.contains(d));
        assert_eq!(union.entries, [(a, 1), (b, 2), (c, 3), (d, 4)]);
        assert_eq!(*union.total(), 10);
    }
}
