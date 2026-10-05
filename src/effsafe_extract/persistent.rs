//! Versioned arrays for the statewalk DP: each DP state owns a version of the
//! extractable-set bit set and of the pure e-nodes' child counters.
//!
//! A version is a whole copy of the array behind an `Rc`; versions created in
//! the current generation (see `new_version`) are updated in place, older
//! ones are copied on write. That makes an update O(n) in the region size
//! rather than the O(log n) of a persistent tree, but regions are small (the
//! largest in eggcc's benchmarks has a few hundred e-classes, a handful of
//! words) and measurements showed the copy-on-write version at least as fast
//! as the B-tree the C++ implementation used, on real benchmarks and on a
//! synthetic 5000-step statewalk, with far less code.

use std::rc::Rc;

pub type Id = u32;

#[derive(Default)]
struct Versions {
    arrays: Vec<Rc<Vec<u32>>>,
    /// Versions created in the current generation may be updated in place.
    generation: u32,
    created_in: Vec<u32>,
}

impl Versions {
    fn init(&mut self, data: &[u32]) -> Id {
        self.arrays.clear();
        self.created_in.clear();
        self.generation = 0;
        self.arrays.push(Rc::new(data.to_vec()));
        self.created_in.push(0);
        0
    }

    fn new_version(&mut self) {
        self.generation += 1;
    }

    fn get(&self, version: Id, i: usize) -> u32 {
        self.arrays[version as usize][i]
    }

    /// Set element `i`, in place if `version` is from the current generation,
    /// otherwise in a copy. Returns the version holding the new value.
    fn set(&mut self, version: Id, i: usize, value: u32) -> Id {
        if self.created_in[version as usize] == self.generation {
            Rc::make_mut(&mut self.arrays[version as usize])[i] = value;
            return version;
        }
        let mut copy = (*self.arrays[version as usize]).clone();
        copy[i] = value;
        self.arrays.push(Rc::new(copy));
        self.created_in.push(self.generation);
        (self.arrays.len() - 1) as Id
    }
}

/// Persistent array of counters that only ever decrease (one `u32` each).
#[derive(Default)]
pub struct PersistentCounters {
    versions: Versions,
}

impl PersistentCounters {
    pub fn init(&mut self, data: &[u32]) -> Id {
        self.versions.init(data)
    }

    pub fn new_version(&mut self) {
        self.versions.new_version();
    }

    /// Decrement counter `i` (saturating at zero). Returns the new version and
    /// the counter's value *before* the decrement.
    pub fn decrement(&mut self, version: Id, i: usize) -> (Id, u32) {
        let value = self.versions.get(version, i);
        if value == 0 {
            return (version, 0);
        }
        (self.versions.set(version, i, value - 1), value)
    }
}

/// Persistent bit set (one `u32` word per 32 bits).
#[derive(Default)]
pub struct PersistentBitSet {
    versions: Versions,
}

impl PersistentBitSet {
    pub fn init(&mut self, data: &[u32]) -> Id {
        // `data` holds one bit per element, as in `persistent.rs`.
        let words: Vec<u32> = data
            .chunks(32)
            .map(|chunk| {
                chunk
                    .iter()
                    .enumerate()
                    .fold(0u32, |w, (j, &b)| w | ((b & 1) << j))
            })
            .collect();
        self.versions.init(&words)
    }

    pub fn new_version(&mut self) {
        self.versions.new_version();
    }

    pub fn contains(&self, version: Id, i: usize) -> bool {
        (self.versions.get(version, i / 32) >> (i % 32)) & 1 != 0
    }

    /// Set bit `i`. Returns the new version and whether the bit was already set.
    pub fn insert(&mut self, version: Id, i: usize) -> (Id, bool) {
        let word = self.versions.get(version, i / 32);
        let new_word = word | (1 << (i % 32));
        if new_word == word {
            return (version, true);
        }
        (self.versions.set(version, i / 32, new_word), false)
    }
}
