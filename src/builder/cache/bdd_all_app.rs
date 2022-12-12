//! Apply cache for BDD operations that stores all ITEs
use fnv::FnvHashMap;

use crate::repr::bdd::BddPtr;

use super::{ite::Ite, LruTable};

const INITIAL_CAPACITY: usize = 8; // given as a power of two

/// An Ite structure, assumed to be in standard form.


/// The top-level data structure that caches applications
pub struct BddAllTable {
    /// a vector of applications, indexed by the top label of the first pointer.
    table: Vec<FnvHashMap<(BddPtr, BddPtr, BddPtr), BddPtr>>,
}

impl LruTable for BddAllTable {
    /// Push a new apply table for a new variable
    fn push_table(&mut self) {
        self.table.push(FnvHashMap::default());
    }

    /// Insert an ite (f, g, h) into the apply table
    fn insert(&mut self, ite: Ite, res: BddPtr) {
        match ite {
            Ite::IteChoice { f, g, h } | Ite::IteComplChoice { f, g, h } => {
                // convert the ITE into a canonical form
                while f.var().value_usize() >= self.table.len() {
                    self.push_table();
                }
                let compl = ite.is_compl_choice();
                self.table[f.var().value() as usize].insert((f, g, h), if compl { res.compl() } else { res });
            },
            Ite::IteConst(_) => (), // do not cache base-cases
        }
    }

    fn get(&mut self, ite: Ite) -> Option<BddPtr> {
        match ite {
            Ite::IteChoice {f, g, h} | Ite::IteComplChoice { f, g, h } => {
                while f.var().value_usize() >= self.table.len() {
                    self.push_table();
                }
                let r = self.table[f.var().value() as usize].get(&(f, g, h));
                let compl = ite.is_compl_choice();
                if compl {
                    r.map(|v| v.compl())
                } else {
                    r.cloned()
                }
               },
               Ite::IteConst(f) => Some(f)
            }
        }

    }


impl BddAllTable {
    pub fn new(num_vars: usize) -> BddAllTable {
        BddAllTable {
            table: (0..num_vars).map(|_| FnvHashMap::default()).collect(),
        }
    }

}
