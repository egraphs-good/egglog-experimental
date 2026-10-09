//! Versioned sets and counters for the statewalk dynamic program.
//!
//! Call `new_version` before branching from a saved version. Updates within
//! a generation may change that generation's version; older versions remain valid.

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

/// Versioned counters that only decrease.
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

/// Versioned set of bit indices.
#[derive(Default)]
pub struct PersistentBitSet {
    versions: Versions,
}

impl PersistentBitSet {
    pub fn init(&mut self, data: &[u32]) -> Id {
        // Each input element contributes its low bit.
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
