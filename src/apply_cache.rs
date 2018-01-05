//! Stores BDD applications in an LRU cache.
use bdd::*;
use util::*;
use std::hash::{Hasher, Hash};
use twox_hash::XxHash;
use fnv::FnvHasher;

const LOAD_FACTOR: f64 = 0.7;
const INITIAL_CAPACITY: usize = 16392;
const GROWTH_RATE: usize = 64;
const MAX_OFFSET: usize = 5;

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct ApplyCacheStats {
    lookup_count: usize,
    miss_count: usize,
}

impl ApplyCacheStats {
    fn new() -> ApplyCacheStats {
        ApplyCacheStats {
            miss_count: 0,
            lookup_count: 0,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct BddCacheStats {
    lookup_count: usize,
    miss_count: usize,
    avg_probe: f64,
    num_applications: usize,
}

impl BddCacheStats {
    fn new() -> BddCacheStats {
        BddCacheStats {
            miss_count: 0,
            lookup_count: 0,
            avg_probe: 0.0,
            num_applications: 0,
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct ApplyOp(pub Op, pub BddPtr, pub BddPtr);

/// Data structure stored in the subtables
#[derive(Debug, Hash, Clone)]
struct Element<K, V>
where
    K: Hash + Clone + Eq + PartialEq,
    V: Eq + PartialEq + Clone,
{
    key: K,
    val: V,
    occupied: bool,
    offset: u32,
}

impl<K, V> Element<K, V>
where
    K: Hash + Clone + Eq + PartialEq,
    V: Eq + PartialEq + Clone,
{
    fn new(key: K, val: V) -> Element<K, V> {
        Element {
            key: key,
            val: val,
            occupied: true,
            offset: 0,
        }
    }
}

/// Each variable has an associated sub-table
pub struct SubTable<K, V>
where
    K: Hash + Clone + Eq + PartialEq,
    V: Eq + PartialEq + Clone,
{
    tbl: Vec<Element<K, V>>,
    len: usize,
    cap: usize,
    stat: ApplyCacheStats,
}

struct SubTableIter<'a, K, V>
where
    K: Hash + Clone + Eq + PartialEq + 'a,
    V: Eq + PartialEq + Clone + 'a,
{
    tbl: &'a SubTable<K, V>,
    pos: usize,
}

impl<'a, K, V> Iterator for SubTableIter<'a, K, V>
where
    K: Hash + Clone + Eq + PartialEq + 'a,
    V: Eq + PartialEq + Clone + 'a,
{
    type Item = &'a Element<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.tbl.tbl.len() {
            None
        } else {
            self.pos += 1;
            let itm = self.tbl.tbl[self.pos - 1].clone();
            if itm.occupied {
                Some(&self.tbl.tbl[self.pos - 1])
            } else {
                self.next()
            }
        }
    }
}

#[derive(PartialEq, Eq)]
enum InsertResult {
    InsufficientSpace,
    MaxProbeHit,
    Ok,
}

impl<K, V> SubTable<K, V>
where
    K: Hash + Clone + Eq + PartialEq,
    V: Eq + PartialEq + Clone,
{
    pub fn new(minimum_size: usize) -> SubTable<K, V> {
        let tbl_sz = ((minimum_size as f64 * (1.0 + LOAD_FACTOR)) as usize).next_power_of_two();
        let v: Vec<Element<K, V>> = zero_vec(tbl_sz);
        SubTable {
            tbl: v,
            len: 0,
            cap: tbl_sz,
            stat: ApplyCacheStats::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn insert(&mut self, key: K, val: V) -> () {
        let mut cur_status = InsertResult::MaxProbeHit;
        while cur_status != InsertResult::Ok {
            let r = self.insert_helper(key.clone(), val.clone());
            match r {
                InsertResult::Ok => cur_status = InsertResult::Ok,
                InsertResult::InsufficientSpace => {
                    let mut grow_status = InsertResult::MaxProbeHit;
                    while grow_status != InsertResult::Ok {
                        grow_status = self.grow();
                    }
                }
                InsertResult::MaxProbeHit => {
                    let mut grow_status = InsertResult::MaxProbeHit;
                    while grow_status != InsertResult::Ok {
                        grow_status = self.grow();
                    }
                }
            }
        }
    }

    fn insert_helper(&mut self, key: K, val: V) -> InsertResult {
        if (self.len + 1) as f64 > (self.cap as f64 * LOAD_FACTOR) {
            return InsertResult::InsufficientSpace;
        }

        let mut hasher = XxHash::default();
        key.hash(&mut hasher);
        let hash_v = hasher.finish();
        let mut pos = (hash_v as usize) % self.cap;
        let mut searcher = Element::new(key.clone(), val.clone());
        let mut cur_status = InsertResult::Ok;
        loop {
            if self.tbl[pos].occupied {
                // first, check if they are equal.
                if self.tbl[pos].key == key {
                    return cur_status;
                } else {
                }
                // they are not equal, see if we should swap for the closer one
                if self.tbl[pos].offset < searcher.offset {
                    // swap the searcher with the current element
                    let tmp = searcher;
                    searcher = self.tbl[pos].clone();
                    self.tbl[pos] = tmp;
                } else {
                    searcher.offset += 1;
                }

                if searcher.offset > MAX_OFFSET as u32 {
                    cur_status = InsertResult::MaxProbeHit;
                }
            } else {
                // found an open spot, insert
                self.tbl[pos] = searcher;
                self.len += 1;
                return cur_status;
            }
            pos = (pos + 1) % self.cap;
        }
    }

    fn iter<'a>(&'a self) -> SubTableIter<'a, K, V> {
        SubTableIter { tbl: self, pos: 0 }
    }

    pub fn get(&mut self, key: K) -> Option<V> {
        self.stat.lookup_count += 1;
        let mut hasher = XxHash::default();
        key.hash(&mut hasher);
        let hash_v = hasher.finish();
        let mut pos = (hash_v as usize) % self.cap;
        for _ in 0..MAX_OFFSET {
            if self.tbl[pos].key == key {
                return Some(self.tbl[pos].val.clone());
            }
            pos = (pos + 1) % self.cap;
        }
        self.stat.miss_count += 1;
        return None;
    }

    /// grow the hashtable to accomodate more elements
    fn grow(&mut self) -> InsertResult {
        println!("growing");
        let new_sz = self.cap * GROWTH_RATE;
        let new_v = zero_vec(new_sz);
        let mut new_tbl = SubTable {
            tbl: new_v,
            len: 0,
            cap: new_sz,
            stat: ApplyCacheStats::new(),
        };

        for i in self.iter() {
            match new_tbl.insert_helper(i.key.clone(), i.val.clone()) {
                InsertResult::Ok => (),
                InsertResult::InsufficientSpace => panic!("growth rate too low"),
                InsertResult::MaxProbeHit => {
                    return InsertResult::MaxProbeHit;
                }
            }
        }

        // copy new_tbl over the current table
        self.tbl = new_tbl.tbl;
        self.cap = new_tbl.cap;
        self.len = new_tbl.len;
        // don't update the stats; we want to keep those
        return InsertResult::Ok;
    }

    fn avg_offset(&self) -> f64 {
        let mut offs: usize = 0;
        if self.len == 0 {
            return 0.0;
        }

        for i in self.iter() {
            offs += i.offset as usize;
        }
        offs as f64 / (self.len as f64)
    }

    pub fn get_stats(&self) -> ApplyCacheStats {
        self.stat.clone()
    }
}

/// The top-level data structure which caches applications
pub struct BddApplyTable {
    /// a table of Ite triples
    tables: Vec<SubTable<(BddPtr, BddPtr, BddPtr), BddPtr>>,
}

impl BddApplyTable {
    pub fn new(num_vars: usize) -> BddApplyTable {
        let mut tbl = BddApplyTable {
            tables: Vec::with_capacity(num_vars),
        };
        for _ in 0..num_vars {
            tbl.tables.push(SubTable::new(INITIAL_CAPACITY));
        }
        tbl
    }

    /// Insert an operation into the apply table. Note that operations are
    /// normalized by first sorting the sub-BDDs such that BDD A occurs first
    /// in the ordering; this increases cache hit rate and decreases duplicate
    /// storage
    pub fn insert(&mut self, f: BddPtr, g: BddPtr, h: BddPtr, res: BddPtr) -> () {
        let tbl = f.var() as usize;
        self.tables[tbl].insert((f, g, h), res);
    }

    pub fn get(&mut self, f: BddPtr, g: BddPtr, h: BddPtr) -> Option<BddPtr> {
        let tbl = f.var() as usize;
        self.tables[tbl].get((f, g, h))
    }

    pub fn get_stats(&self) -> BddCacheStats {
        let mut st = BddCacheStats::new();
        let mut offset = 0.0;
        let mut c = 0.0;
        for tbl in self.tables.iter() {
            let stats = tbl.get_stats();
            st.lookup_count += stats.lookup_count;
            st.miss_count += stats.miss_count;
            offset += tbl.avg_offset();
            st.num_applications += tbl.len();
            c += 1.0;
        }
        st.avg_probe = offset / c;
        st
    }
}

#[test]
fn apply_cache_simple() {
    let mut tbl = BddApplyTable::new(10);
    for var in 0..10 {
        for i in 0..100000 {
            let f = BddPtr::new(VarLabel::new(var), TableIndex::new(i));
            let g = BddPtr::new(VarLabel::new(var + 1), TableIndex::new(i));
            let h = BddPtr::true_node();
            let result = BddPtr::new(VarLabel::new(var), TableIndex::new(i));
            tbl.insert(f, g, h, result);
        }
    }
    for var in 0..10 {
        for i in 0..100000 {
            let f = BddPtr::new(VarLabel::new(var), TableIndex::new(i));
            let g = BddPtr::new(VarLabel::new(var + 1), TableIndex::new(i));
            let h = BddPtr::true_node();
            let result = BddPtr::new(VarLabel::new(var), TableIndex::new(i));
            tbl.insert(f, g, h, result);
            assert_eq!(tbl.get(f, g, h).unwrap(), result);
        }
    }
}
