//! Primary interface for manipulating and constructing BDDs. Contains the BDD
//! manager, which manages the global state necessary for constructing canonical
//! binary decision diagrams.

use crate::repr::cnf::UnitPropagate;
use crate::{
    repr,
    backing_store::bdd_table_robinhood::BddTable,
    backing_store::BackingCacheStats,
    builder::cache::bdd_app::*,
    builder::var_order::VarOrder,
    builder::repr::builder_bdd::*,
    repr::logical_expr::LogicalExpr,
    repr::cnf::Cnf,
    repr::model,
    repr::var_label::VarLabel,
    repr::var_label::Literal,
};


use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::fmt::Debug;
use num::traits::Num;
use rand::rngs::ThreadRng;
use rand::Rng;

use super::bdd_plan::BddPlan;

#[derive(Eq, PartialEq, Debug)]
struct CompiledCNF {
    ptr: BddPtr,
    sz: usize,
}

// The priority queue depends on `Ord`.
// Explicitly implement the trait so the queue becomes a min-heap
// instead of a max-heap.
impl Ord for CompiledCNF {
    fn cmp(&self, other: &Self) -> Ordering {
        // Notice that the we flip the ordering on costs.
        // In case of a tie we compare positions - this step is necessary
        // to make implementations of `PartialEq` and `Ord` consistent.
        other
            .sz
            .cmp(&self.sz)
            .then_with(|| self.ptr.raw().cmp(&other.ptr.raw()))
    }
}

// `PartialOrd` needs to be implemented as well.
impl PartialOrd for CompiledCNF {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
pub struct Assignment {
    assignments: Vec<bool>,
}

impl Assignment {
    pub fn new(assignments: Vec<bool>) -> Assignment {
        Assignment { assignments }
    }

    pub fn get_assignment(&self, var: VarLabel) -> bool {
        return self.assignments[var.value() as usize];
    }
}

/// Weighted model counting parameters for a BDD. It primarily is a storage for
/// the weight on each variable.
#[derive(Debug)]
pub struct BddWmc<T: Num + Clone + Debug + Copy> {
    pub zero: T,
    pub one: T,
    /// a vector which maps variable labels to `(low, high)`
    /// valuations.
    var_to_val: Vec<Option<(T, T)>>,
}

impl<T: Num + Clone + Debug + Copy> BddWmc<T> {
    /// Generates a new `BddWmc` with a default `var_to_val`; it is private because we
    /// do not want to expose the structure of the associative array
    pub fn new_with_default(zero: T, one: T, var_to_val: HashMap<VarLabel, (T, T)>) -> BddWmc<T> {
        let mut var_to_val_vec: Vec<Option<(T, T)>> = vec![None; var_to_val.len()];
        for (key, value) in var_to_val.iter() {
            var_to_val_vec[key.value_usize()] = Some(*value);
        }
        BddWmc {
            zero: zero,
            one: one,
            var_to_val: var_to_val_vec,
        }
    }

    /// Generate a new `BddWmc` with no associations
    pub fn new(zero: T, one: T) -> BddWmc<T> {
        BddWmc {
            zero: zero,
            one: one,
            var_to_val: Vec::new(),
        }
    }

    /// get the weight of an asignment
    pub fn get_weight(&self, assgn: &[Literal]) -> T {
        let mut prod = self.one;
        for lit in assgn.iter() {
            if lit.get_polarity() {
                prod = prod * self.var_to_val[lit.get_label().value_usize()].unwrap().1
            } else {
                prod = prod * self.var_to_val[lit.get_label().value_usize()].unwrap().0
            }
        }
        return prod;
    }

    pub fn set_weight(&mut self, lbl: VarLabel, low: T, high: T) -> () {
        let n = lbl.value_usize();
        while n >= self.var_to_val.len() {
            self.var_to_val.push(None);
        }
        self.var_to_val[n] = Some((low, high));
    }

    pub fn get_var_weight(&self, label: VarLabel) -> &(T, T) {
        return &(self.var_to_val[label.value_usize()]).as_ref().unwrap();
    }
}

/// An auxiliary data structure for tracking statistics about BDD manager
/// performance (for fine-tuning)
struct BddManagerStats {
    /// For now, always track the number of recursive calls. In the future,
    /// this should probably be gated behind a debug build (since I suspect
    /// it may have non-trivial performance overhead and synchronization cost)
    num_recursive_calls: usize,
}

impl BddManagerStats {
    pub fn new() -> BddManagerStats {
        BddManagerStats {
            num_recursive_calls: 0,
        }
    }
}

pub struct BddManager {
    compute_table: BddTable,
    apply_table: BddApplyTable,
    stats: BddManagerStats,
}

impl BddManager {
    /// Make a BDD manager with a default variable ordering
    pub fn new_default_order(num_vars: usize) -> BddManager {
        let default_order = VarOrder::linear_order(num_vars);
        BddManager::new(default_order)
    }

    /// Clear the internal scratch space for a BddPtr
    fn clear_scratch(&mut self, ptr: BddPtr) -> () {
        if ptr.is_const() {
            return;
        } else {
            if self.compute_table.get_scratch(ptr).is_none() {
                return;
            } else {
                self.compute_table.set_scratch(ptr, None);
                self.clear_scratch(self.low(ptr));
                self.clear_scratch(self.high(ptr));
            }
        }
    }

    /// Fill the scratch space of each node with a counter that 
    /// indexes an in-order left-first depth-first traversal
    /// returns the new count (will be #nodes in the BDD at the end)
    /// 
    /// Pre-condition: cleared scratch 
    fn unique_label_nodes(&mut self, ptr: BddPtr, count: usize) -> usize {
        if ptr.is_const() {
            return count;
        } else {
            if self.compute_table.get_scratch(ptr).is_some() {
                return count;
            } else {
                self.compute_table.set_scratch(ptr, Some(count));
                let new_count = self.unique_label_nodes(self.low(ptr), count+1);
                self.unique_label_nodes(self.high(ptr), new_count)
            }
        }
    }

    /// Walks `ptr`, pushes the nodes onto `v` and constructs a new finalized BDD
    /// Returns the so far (current index )
    /// 
    /// Pre-condition: cleared scratch 
    fn finalize_h(&mut self, v: &mut Vec<repr::bdd::Bdd>, ptr: BddPtr) -> repr::bdd::BddPtr {
        if ptr.is_true() {
            return repr::bdd::BddPtr::new(0);
        } else if ptr.is_false() {
            return repr::bdd::BddPtr::new(1);
        } 

        let idx = match self.compute_table.get_scratch(ptr) {
            Some(v) => v,
            None => {
                let (l, h) = if ptr.is_compl() {
                    (self.low(ptr).neg(), self.high(ptr).neg())
                } else {
                    (self.low(ptr), self.high(ptr))
                };
                let l = self.finalize_h(v, l);
                let h = self.finalize_h(v, h);
                let new_n = repr::bdd::Bdd::Node { var: ptr.label(), low: l, high: h };
                v.push(new_n);
                let new_idx = v.len() - 1;
                self.compute_table.set_scratch(ptr, Some(new_idx));
                new_idx
            }
        };
        repr::bdd::BddPtr::new(idx)
    }

    /// Generate the finalized output BDD
    pub fn finalize(&mut self, ptr: BddPtr) -> repr::bdd::FinalizedBDD {
        use repr::bdd::*;
        let sz = self.unique_label_nodes(ptr, 0);
        let mut v = Vec::with_capacity(sz);
        v.push(Bdd::True);
        v.push(Bdd::False);
        let bdd = self.finalize_h(&mut v, ptr);
        self.clear_scratch(ptr);
        repr::bdd::FinalizedBDD::new(bdd, v, self.get_order().clone())
    }

    /// Creates a new variable manager with the specified order
    pub fn new(order: VarOrder) -> BddManager {
        let l = order.num_vars();
        BddManager {
            compute_table: BddTable::new(order),
            apply_table: BddApplyTable::new(l),
            stats: BddManagerStats::new(),
        }
    }

    /// Returns the number of variables in the manager
    pub fn num_vars(&self) -> usize {
        return self.get_order().num_vars();
    }

    /// Generate a new variable which was not in the original order. Places the
    /// new variable at the end of the current order. Returns the label of the
    /// new variable.
    pub fn new_var(&mut self) -> VarLabel {
        self.apply_table.push_table();
        self.compute_table.new_last()
    }

    /// Get the current variable order
    pub fn get_order(&self) -> &VarOrder {
        self.compute_table.order()
    }

    /// Dereference a BddPtr into a Bdd
    fn deref_bdd(&self, ptr: BddPtr) -> Bdd {
        self.compute_table.deref(ptr)
    }

    /// Fetch the BDD pointed to by the low-node of `ptr`
    /// panics on constant BDDs
    pub fn low(&self, ptr: BddPtr) -> BddPtr {
        assert!(!ptr.is_const(), "Attempting to get low pointer of constant BDD");
        let b = self.deref_bdd(ptr).into_node();
        b.low
    }

    /// Fetch the BDD pointed to by the high-node of `ptr`, panics on constant
    /// BDDs
    pub fn high(&self, ptr: BddPtr) -> BddPtr {
        assert!(!ptr.is_const(), "Attempting to get high pointer of constant BDD");
        let b = self.deref_bdd(ptr).into_node();
        b.high
    }

    /// Get a pointer to the variable with label `lbl` and polarity `polarity`
    pub fn var(&mut self, lbl: VarLabel, polarity: bool) -> BddPtr {
        let bdd = BddNode::new(BddPtr::false_node(), BddPtr::true_node(), lbl);
        let r = self.get_or_insert(bdd);
        if polarity {
            r
        } else {
            r.neg()
        }
    }

    pub fn true_ptr(&self) -> BddPtr {
        BddPtr::true_node()
    }

    pub fn false_ptr(&self) -> BddPtr {
        BddPtr::false_node()
    }

    /// True if the BddPtr is true
    pub fn is_true(&self, ptr: BddPtr) -> bool {
        ptr.is_true()
    }

    pub fn is_false(&self, ptr: BddPtr) -> bool {
        ptr.is_false()
    }

    /// Retrieves the top variable of the BDD
    pub fn topvar(&self, ptr: BddPtr) -> VarLabel {
        let bdd = self.deref_bdd(ptr).into_node();
        bdd.var
    }

    /// normalizes and fetches a node from the store
    fn get_or_insert(&mut self, bdd: BddNode) -> BddPtr {
        if bdd.high.is_compl() {
            let bdd = Bdd::new_node(bdd.low.neg(), bdd.high.neg(), bdd.var);
            self.compute_table.get_or_insert(bdd).neg()
        } else {
            let bdd = Bdd::new_node(bdd.low, bdd.high, bdd.var);
            self.compute_table.get_or_insert(bdd)
        }
    }

    pub fn to_string_debug(&self, ptr: BddPtr) -> String {
        fn print_bdd_helper(t: &BddManager, ptr: BddPtr) -> String {
            match ptr.ptr_type() {
                PointerType::PtrTrue => String::from("T"),
                PointerType::PtrFalse => String::from("F"),
                PointerType::PtrNode => {
                    let l_p = if ptr.is_compl() {
                        t.low(ptr).neg()
                    } else {
                        t.low(ptr)
                    };
                    let h_p = if ptr.is_compl() {
                        t.high(ptr).neg()
                    } else {
                        t.high(ptr)
                    };
                    let l_s = print_bdd_helper(t, l_p);
                    let h_s = print_bdd_helper(t, h_p);
                    format!("({}, {}, {})", ptr.var(), h_s, l_s)
                }
            }
        }
        print_bdd_helper(self, ptr)
    }

    pub fn negate(&mut self, ptr: BddPtr) -> BddPtr {
        ptr.neg()
    }

    /// Print a debug form of the BDD with the label remapping given by `map`
    pub fn print_bdd_lbl(&self, ptr: BddPtr, map: &HashMap<VarLabel, VarLabel>) -> String {
        use crate::builder::repr::builder_bdd::PointerType::*;
        fn print_bdd_helper(
            t: &BddManager,
            ptr: BddPtr,
            map: &HashMap<VarLabel, VarLabel>,
        ) -> String {
            match ptr.ptr_type() {
                PtrTrue => String::from("T"),
                PtrFalse => String::from("T"),
                PtrNode => {
                    let l_p = t.low(ptr);
                    let h_p = t.high(ptr);
                    let l_s = print_bdd_helper(t, l_p, map);
                    let r_s = print_bdd_helper(t, h_p, map);
                    format!(
                        "({:?}, {}{}, {}{})",
                        map.get(&ptr.label()).unwrap().value(),
                        if l_p.is_compl() { "!" } else { "" },
                        l_s,
                        if h_p.is_compl() { "!" } else { "" },
                        r_s
                    )
                }
            }
        }
        let s = print_bdd_helper(self, ptr, map);
        format!("{}{}", if ptr.is_compl() { "!" } else { "" }, s)
    }

    /// Compose `g` into `f` by substituting for `lbl`
    pub fn compose(&mut self, f: BddPtr, lbl: VarLabel, g: BddPtr) -> BddPtr {
        // TODO this can be optimized with a specialized implementation to make
        // it a single traversal
        let var = self.var(lbl, true);
        let iff = self.iff(var, g);
        let a = self.and(iff, f);
        let r = self.exists(a, lbl);
        r
    }

    /// true if `a` represents a variable (both high and low are constant)
    pub fn is_var(&self, ptr: BddPtr) -> bool {
        match ptr.ptr_type() {
            PointerType::PtrNode => {
                let b = self.compute_table.deref(ptr).into_node();
                b.low.is_const() && b.high.is_const()
            }
            _ => false,
        }
    }

    // condition a BDD *only* if the top variable is `v`; used in `ite`
    fn condition_essential(&self, f: BddPtr, lbl: VarLabel, v: bool) -> BddPtr {
        if f.is_const() || f.var() != lbl.value() {
            return f;
        };
        let r = if v { self.high(f) } else { self.low(f) };
        if f.is_compl() {
            r.neg()
        } else {
            r
        }
    }

    fn ite_helper(&mut self, f: BddPtr, g: BddPtr, h: BddPtr) -> BddPtr {
        self.stats.num_recursive_calls += 1;
        // a wise man once said: there are parts of the code that are easier to
        // prove correct than they are to debug or test. This is one of those
        // parts.  Is it proven correct? Unfortunately, no.
        //
        // standardize
        // See pgs. 115-117 of "Algorithms and Data Structures in VLSI Design"
        // attempt a base case
        match self.apply_table.get(f, g, h) {
            Some(v) => return v,
            None => (),
        };
        let f_orig = f;
        let g_orig = g;
        let h_orig = h;

        match (f, g, h) {
            (_, g, h) if g.is_false() && h.is_false() => return BddPtr::false_node(),
            (_, g, h) if g.is_true() && h.is_true() => return BddPtr::true_node(),
            (f, g, h) if g.is_true() && h.is_false() => return f,
            (f, g, h) if g.is_false() && h.is_true() => return f.neg(),
            (f, g, _) if f.is_true() => return g,
            (f, _, h) if f.is_false() => return h,
            (_, g, h) if g == h => return g,
            _ => (),
        };

        // attempt to place the variable that comes first in the order as f
        let (f, g, h) = match (f, g, h) {
            (f, g, h) if g.is_true() && self.get_order().lt(h.label(), f.label()) => (h, g, f),
            (f, g, h) if h.is_false() && self.get_order().lt(g.label(), f.label()) => (g, f, h),
            (f, g, h) if h.is_true() && self.get_order().lt(g.label(), f.label()) => {
                (g.neg(), f.neg(), h)
            }
            (f, g, h) if g.is_false() && self.get_order().lt(h.label(), f.label()) => {
                (h.neg(), g, f.neg())
            }
            (f, g, h) if g == h && self.get_order().lt(g.label(), f.label()) => (g, f, f.neg()),
            _ => (f, g, h),
        };

        // ok the work!
        // find the first essential variable for f, g, or h
        let lbl = self.get_order().first_essential(f, g, h);
        let fx = self.condition_essential(f, lbl, true);
        let gx = self.condition_essential(g, lbl, true);
        let hx = self.condition_essential(h, lbl, true);
        let fxn = self.condition_essential(f, lbl, false);
        let gxn = self.condition_essential(g, lbl, false);
        let hxn = self.condition_essential(h, lbl, false);
        let t = self.ite(fx, gx, hx);
        let f = self.ite(fxn, gxn, hxn);

        if t == f {
            return t;
        };

        // now we have a new BDD
        let node = BddNode {
            low: f,
            high: t,
            var: lbl,
        };
        let r = self.get_or_insert(node);
        self.apply_table.insert(f_orig, g_orig, h_orig, r);
        r
    }

    /// if f then g else h
    pub fn ite(&mut self, f: BddPtr, g: BddPtr, h: BddPtr) -> BddPtr {
        let r = self.ite_helper(f, g, h);
        r
    }

    /// Produce a new BDD that is the result of conjoining `f` and `g`
    /// ```
    /// # use rsdd::builder::bdd_builder::BddManager;
    /// # use rsdd::repr::var_label::VarLabel;
    /// let mut mgr = BddManager::new_default_order(10);
    /// let lbl_a = mgr.new_var();
    /// let a = mgr.var(lbl_a, true);
    /// let a_and_not_a = mgr.and(a, a.neg());
    /// assert!(mgr.is_false(a_and_not_a));
    /// ```
    pub fn and(&mut self, f: BddPtr, g: BddPtr) -> BddPtr {
        self.stats.num_recursive_calls += 1;
        // base case
        let reg_f = f.regular();
        let reg_g = g.regular();
        if reg_f == reg_g {
            if f == g {
                return f;
            } else {
                return BddPtr::false_node();
            }
        }
        if reg_f.is_true() {
            if f.is_true() {
                return g;
            } else {
                return f;
            }
        }
        if reg_g.is_true() {
            if g.is_true() {
                return f;
            } else {
                return g;
            }
        }

        // now, both of the nodes are not constant
        // normalize the nodes to increase cache efficiency
        //
        // TODO is this a redundant normalization?
        let (f, g, reg_f, _) = if reg_f < reg_g {
            (f, g, reg_f, reg_g)
        } else {
            (g, f, reg_g, reg_f)
        };

        // check the cache
        match self.apply_table.get(f, g, BddPtr::false_node()) {
            Some(v) => {
                return v;
            }
            None => {}
        };

        // now we know that these are nodes, compute the cofactors
        let topf = self.get_order().get(f.label());
        let topg = self.get_order().get(g.label());
        let index; // will hold the top variable
        let mut fv;
        let mut gv;
        let mut fnv;
        let mut gnv;
        if topf <= topg {
            index = f.label();
            fv = self.high(reg_f);
            fnv = self.low(reg_f);
            if f.is_compl() {
                fv = fv.neg();
                fnv = fnv.neg();
            }
        } else {
            index = g.label();
            fv = f;
            fnv = f;
        }

        if topg <= topf {
            gv = self.high(g);
            gnv = self.low(g);
            if g.is_compl() {
                gv = gv.neg();
                gnv = gnv.neg();
            }
        } else {
            gv = g;
            gnv = g;
        }

        // now recurse
        let new_h = self.and(fv, gv);
        let new_l = self.and(fnv, gnv);

        // now normalize the result
        if new_h == new_l {
            return new_h;
        } else {
            let n = BddNode {
                low: new_l,
                high: new_h,
                var: index,
            };
            let r = self.get_or_insert(n);
            self.apply_table.insert(f, g, BddPtr::false_node(), r);
            return r;
        }
    }

    /// Compute the Boolean function `f || g`
    pub fn or(&mut self, f: BddPtr, g: BddPtr) -> BddPtr {
        self.and(f.neg(), g.neg()).neg()
    }

    /// disjoins a list of BDDs
    pub fn or_lst(&mut self, f: &[BddPtr]) -> BddPtr {
        let mut cur_bdd = self.false_ptr();
        for &itm in f {
            cur_bdd = self.or(cur_bdd, itm);
        }
        cur_bdd
    }

    /// disjoins a list of BDDs
    pub fn and_lst(&mut self, f: &[BddPtr]) -> BddPtr {
        let mut cur_bdd = self.true_ptr();
        for &itm in f {
            cur_bdd = self.and(cur_bdd, itm);
        }
        cur_bdd
    }

    /// Compute the Boolean function `f iff g`
    pub fn iff(&mut self, f: BddPtr, g: BddPtr) -> BddPtr {
        self.ite(f, g, g.neg())
    }

    pub fn xor(&mut self, f: BddPtr, g: BddPtr) -> BddPtr {
        self.ite(f, g.neg(), g)
    }

    fn cond_helper(
        &mut self,
        bdd: BddPtr,
        lbl: VarLabel,
        value: bool,
        cache: &mut HashMap<BddPtr, BddPtr>,
    ) -> BddPtr {
        self.stats.num_recursive_calls += 1;
        if self.get_order().lt(lbl, bdd.label()) || bdd.is_const() {
            // we passed the variable in the order, we will never find it
            bdd
        } else if bdd.label() == lbl {
            let node = self.deref_bdd(bdd).into_node();
            let r = if value { node.high } else { node.low };
            if bdd.is_compl() {
                r.neg()
            } else {
                r
            }
        } else {
            // check cache
            match cache.get(&bdd) {
                None => (),
                Some(v) => return *v,
            };

            // recurse on the children
            let n = self.deref_bdd(bdd).into_node();
            let l = self.cond_helper(n.low, lbl, value, cache);
            let h = self.cond_helper(n.high, lbl, value, cache);
            if l == h {
                if bdd.is_compl() {
                    return l.neg();
                } else {
                    return l;
                };
            };
            let res = if l != n.low || h != n.high {
                // cache and return the new BDD
                let new_bdd = BddNode {
                    low: l,
                    high: h,
                    var: bdd.label(),
                };
                let r = self.get_or_insert(new_bdd);
                if bdd.is_compl() {
                    r.neg()
                } else {
                    r
                }
            } else {
                // nothing changed
                bdd
            };
            cache.insert(bdd, res);
            res
        }
    }

    /// Compute the Boolean function `f | var = value`
    pub fn condition(&mut self, bdd: BddPtr, lbl: VarLabel, value: bool) -> BddPtr {
        self.cond_helper(bdd, lbl, value, &mut HashMap::new())
    }

    /// Existentially quantifies out the variable `lbl` from `f`
    pub fn exists(&mut self, bdd: BddPtr, lbl: VarLabel) -> BddPtr {
        // TODO this can be optimized by specializing it
        let v1 = self.condition(bdd, lbl, true);
        let v2 = self.condition(bdd, lbl, false);
        self.or(v1, v2)
    }

    /// evaluates the top element of the data stack on the values found in
    /// `vars`
    pub fn eval_bdd(&self, bdd: BddPtr, assgn: &HashMap<VarLabel, bool>) -> bool {
        fn eval_bdd_helper(man: &BddManager, ptr: BddPtr, assgn: &HashMap<VarLabel, bool>) -> bool {
            if ptr.is_true() {
                return true;
            } else if ptr.is_false() {
                return false;
            }
            let bdd = man.deref_bdd(ptr);
            let r = match bdd {
                Bdd::BddTrue => true,
                Bdd::BddFalse => false,
                Bdd::Node(n) => {
                    let value = assgn.get(&n.var).unwrap();
                    if *value {
                        eval_bdd_helper(man, n.high, assgn)
                    } else {
                        eval_bdd_helper(man, n.low, assgn)
                    }
                }
            };
            if ptr.is_compl() {
                !r
            } else {
                r
            }
        }
        eval_bdd_helper(self, bdd, assgn)
    }

    /// Returns true if `a` == `b`
    pub fn eq_bdd(&self, a: BddPtr, b: BddPtr) -> bool {
        // the magic of BDDs!
        a == b
    }

    pub fn get_backing_store_stats(&self) -> BackingCacheStats {
        self.compute_table.get_stats().clone()
    }

    /// Counts the number of nodes present in the BDD (not including constant nodes)
    /// ```
    /// # use rsdd::builder::bdd_builder::BddManager;
    /// # use rsdd::repr::var_label::VarLabel;
    /// let mut mgr = BddManager::new_default_order(10);
    /// let lbl_a = mgr.new_var();
    /// let lbl_b = mgr.new_var();
    /// let a = mgr.var(lbl_a, true);
    /// let b = mgr.var(lbl_b, true);
    /// let a_and_b = mgr.and(a, b);
    /// // This BDD has size 2, as it looks like (if a then b else false)
    /// assert_eq!(mgr.count_nodes(a_and_b), 2);
    /// ```
    pub fn count_nodes(&mut self, ptr: BddPtr) -> usize {
        let s = self.unique_label_nodes(ptr, 0);
        self.clear_scratch(ptr);
        s
    }

    /// The total number of nodes allocated by the manager
    pub fn total_nodes(&self) -> usize {
        self.compute_table.num_nodes()
    }

    /// Pre-condition: Nodes are unique numbered
    fn wmc_helper<T: Num + Clone + Debug + Copy>(
        &mut self,
        ptr: BddPtr,
        wmc: &BddWmc<T>,
        smooth: bool,
        tbl: &mut Vec<(Option<T>, Option<T>)>, // (non-compl, compl)
    ) -> (T, Option<VarLabel>) {
        match ptr.ptr_type() {
            PointerType::PtrTrue => {
                (wmc.one.clone(), Some(self.get_order().last_var()))
            }
            PointerType::PtrFalse => {
                (wmc.zero.clone(), Some(self.get_order().last_var()))
            }
            PointerType::PtrNode => {
                let idx = self.compute_table.get_scratch(ptr).unwrap();
                // let order = self.get_order();
                let res = match tbl[idx] {
                    (_, Some(v)) if ptr.is_compl() => v,
                    (Some(v), _) if !ptr.is_compl() => v,
                    (cur_reg, cur_compl) => {
                        let bdd = self.deref_bdd(ptr).into_node();
                        let (low, high) = if ptr.is_compl() {
                            (bdd.low.neg(), bdd.high.neg())
                        } else {
                            (bdd.low, bdd.high)
                        };
                        let (mut low_v, low_lvl_op) = self.wmc_helper(low, wmc, smooth, tbl);
                        let (mut high_v, high_lvl_op) = self.wmc_helper(high, wmc, smooth, tbl);
                        let mut low_lvl = low_lvl_op.unwrap();
                        let mut high_lvl = high_lvl_op.unwrap();
                        if smooth {
                            // smooth low
                            while self.get_order().lt(ptr.label(), low_lvl) {
                                let (low_factor, high_factor) = wmc.get_var_weight(low_lvl);
                                low_v = (low_v.clone() * (*low_factor)) + (low_v * (*high_factor));
                                low_lvl = self.get_order().above(low_lvl).unwrap();
                            }
                            // smooth high
                            while self.get_order().lt(ptr.label(), high_lvl) {
                                let (low_factor, high_factor) = wmc.get_var_weight(high_lvl);
                                high_v =
                                    (high_v.clone() * (*low_factor)) + (high_v * (*high_factor));
                                high_lvl = self.get_order().above(high_lvl).unwrap();
                            }
                        }
                        // compute new
                        let (low_factor, high_factor) = wmc.get_var_weight(bdd.var);
                        let res = (low_v * low_factor.clone()) + (high_v * high_factor.clone());
                        tbl[idx] = if ptr.is_compl() {
                            (cur_reg, Some(res))
                        } else {
                            (Some(res), cur_compl)
                        };
                        res
                    }
                };

                if self.get_order().get(ptr.label()) == 0 {
                    (res, None)
                } else {
                    (res, Some(self.get_order().above(ptr.label()).unwrap()))
                }
            }
        }
    }

    /// Weighted-model count
    pub fn wmc<T: Num + Clone + Debug + Copy>(&mut self, ptr: BddPtr, params: &BddWmc<T>) -> T {
        let n = self.unique_label_nodes(ptr, 0);
        let mut v = vec![(None, None); n];

        let (mut v, lvl_op) = self.wmc_helper(ptr, params, true, &mut v);
        let r = if lvl_op.is_none() {
            // no smoothing required
            v
        } else {
            let mut lvl = lvl_op;
            let order = self.get_order();
            while lvl.is_some() {
                let (low_factor, high_factor) = params.get_var_weight(lvl.unwrap());
                v = (v.clone() * (*low_factor)) + (v * (*high_factor));
                lvl = order.above(lvl.unwrap());
            }
            v
        };
        self.clear_scratch(ptr);
        r
    }

    fn sample_h(
        &self,
        ptr: BddPtr,
        rng: &mut ThreadRng,
        wmc: &BddWmc<f64>,
        assgn: &mut Vec<bool>,
        cache: &HashMap<BddPtr, f64>,
        cur_level: usize,
    ) -> () {
        // check for smoothing
        if ptr.is_const() {
            if cur_level == self.num_vars() {
                // base case, return
                return;
            } else {
                let expected = self.get_order().var_at_pos(cur_level);
                let w = wmc.get_var_weight(expected);
                let v: bool = rng.gen_bool(w.1 / (w.0 + w.1));
                assgn[expected.value_usize()] = v;
                return self.sample_h(ptr, rng, wmc, assgn, cache, cur_level + 1);
            }
        }

        // let mut rng = rand::thread_rng();
        let topvar: VarLabel = self.topvar(ptr);
        let expected = self.get_order().var_at_pos(cur_level);
        if topvar != expected {
            // smooth by sampling the expected variable
            let w = wmc.get_var_weight(expected);
            let v: bool = rng.gen_bool(w.1 / (w.0 + w.1));
            assgn[expected.value_usize()] = v;
            self.sample_h(ptr, rng, wmc, assgn, cache, cur_level + 1);
        } else {
            // sample the top variable
            let low = if ptr.is_compl() {
                self.low(ptr).neg()
            } else {
                self.low(ptr)
            };
            let high = if ptr.is_compl() {
                self.high(ptr).neg()
            } else {
                self.high(ptr)
            };
            let w = wmc.get_var_weight(topvar);
            let l_weight = cache.get(&low).unwrap();
            let h_weight = cache.get(&high).unwrap();
            let v: bool = rng.gen_bool((w.1 * h_weight) / (w.0 * l_weight + w.1 * h_weight));
            // let v = if ptr.is_compl() {!v} else {v};
            assgn[topvar.value_usize()] = v;
            if v {
                self.sample_h(high, rng, wmc, assgn, cache, cur_level + 1);
            } else {
                self.sample_h(low, rng, wmc, assgn, cache, cur_level + 1);
            }
        }
    }

    /// Draws a sample from the models of the BDD according to the distribution specified by `wmc`
    pub fn sample(&self, ptr: BddPtr, wmc: &BddWmc<f64>) -> Assignment {
        todo!()
        // let mut rng = rand::thread_rng();
        // let mut r = vec![false; self.num_vars()];
        // let mut cache: HashMap<BddPtr, f64> = HashMap::new();
        // let _z = self.cached_wmc(ptr, &wmc, &mut cache);
        // self.sample_h(ptr, &mut rng, wmc, &mut r, &cache, 0);
        // return Assignment::new(r);
    }

    pub fn from_cnf_with_assignments(&mut self, cnf: &Cnf, assgn: &model::PartialModel) -> BddPtr {
        let clauses = cnf.clauses();
        if clauses.is_empty() {
            return self.true_ptr();
        }
        let mut compiled_heap: BinaryHeap<CompiledCNF> = BinaryHeap::new();
        // push each clause onto the compiled_heap
        for clause in clauses.iter() {
            let mut cur_ptr = self.false_ptr();
            for lit in clause.iter() {
                match assgn.get(lit.get_label()) {
                    None => {
                        let new_v = self.var(lit.get_label(), lit.get_polarity());
                        cur_ptr = self.or(new_v, cur_ptr);
                    }
                    Some(v) if v == lit.get_polarity() => {
                        cur_ptr = self.true_ptr();
                        break;
                    }
                    _ => {
                        continue;
                    }
                }
            }
            let sz = self.count_nodes(cur_ptr);
            compiled_heap.push(CompiledCNF { ptr: cur_ptr, sz });
        }

        while compiled_heap.len() > 1 {
            let CompiledCNF { ptr: ptr1, sz: _sz } = compiled_heap.pop().unwrap();
            let CompiledCNF { ptr: ptr2, sz: _sz } = compiled_heap.pop().unwrap();
            let ptr = self.and(ptr1, ptr2);
            // let sz = self.count_nodes(ptr);
            let sz = self.count_nodes(ptr);
            compiled_heap.push(CompiledCNF { ptr, sz })
        }

        let CompiledCNF { ptr, sz: _sz } = compiled_heap.pop().unwrap();
        return ptr;
    }

    /// Compile a BDD from a CNF
    pub fn from_cnf(&mut self, cnf: &Cnf) -> BddPtr {
        let mut cvec: Vec<BddPtr> = Vec::with_capacity(cnf.clauses().len());
        if cnf.clauses().is_empty() {
            return BddPtr::true_node();
        }
        // check if there is an empty clause -- if so, UNSAT
        if cnf.clauses().iter().find(|x| x.is_empty()).is_some() {
            return BddPtr::false_node();
        }

        // sort the clauses based on a best-effort bottom-up ordering of clauses
        let mut cnf_sorted = cnf.clauses().to_vec();
        let order = self.get_order();
        cnf_sorted.sort_by(|c1, c2| {
            // order the clause with the first-most variable last
            let fst1 = c1
                .iter()
                .max_by(|l1, l2| {
                    if order.lt(l1.get_label(), l2.get_label()) {
                        Ordering::Less
                    } else {
                        Ordering::Equal
                    }
                })
                .unwrap();
            let fst2 = c2
                .iter()
                .max_by(|l1, l2| {
                    if order.lt(l1.get_label(), l2.get_label()) {
                        Ordering::Less
                    } else {
                        Ordering::Equal
                    }
                })
                .unwrap();
            if order.lt(fst1.get_label(), fst2.get_label()) {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        });

        for lit_vec in cnf_sorted.iter() {
            let (vlabel, val) = (lit_vec[0].get_label(), lit_vec[0].get_polarity());
            let mut bdd = self.var(vlabel, val);
            for i in 1..lit_vec.len() {
                let (vlabel, val) = (lit_vec[i].get_label(), lit_vec[i].get_polarity());
                let var = self.var(vlabel, val);
                bdd = self.or(bdd, var);
            }
            cvec.push(bdd);
        }
        // now cvec has a list of all the clauses; collapse it down
        fn helper(vec: &[BddPtr], man: &mut BddManager) -> Option<BddPtr> {
            if vec.len() == 0 {
                None
            } else if vec.len() == 1 {
                return Some(vec[0]);
            } else {
                let (l, r) = vec.split_at(vec.len() / 2);
                let sub_l = helper(l, man);
                let sub_r = helper(r, man);
                match (sub_l, sub_r) {
                    (None, None) => None,
                    (Some(v), None) | (None, Some(v)) => Some(v),
                    (Some(l), Some(r)) => Some(man.and(l, r)),
                }
            }
        }
        let r = helper(&cvec, self);
        if r.is_none() {
            return BddPtr::true_node();
        } else {
            return r.unwrap();
        }
    }

    pub fn print_stats(&self) -> () {
        // let compute_stats = self.get_backing_store_stats();
        // let apply_stats = self.apply_table.get_stats();
        // println!("BDD Manager Stats\nCompute hit count: {}\nCompute lookup count: {}\nCompute total elements: {}\nCompute average offset: {}\nApply lookup: {}\nApply miss: {}\nApply evictions: {}",
        // compute_stats.hit_count, compute_stats.lookup_count, compute_stats.num_elements, compute_stats.avg_offset, apply_stats.lookup_count, apply_stats.miss_count, apply_stats.conflict_count);
    }

    pub fn from_boolexpr(&mut self, expr: &LogicalExpr) -> BddPtr {
        match expr {
            &LogicalExpr::Literal(lbl, polarity) => self.var(VarLabel::new(lbl as u64), polarity),
            &LogicalExpr::And(ref l, ref r) => {
                let r1 = self.from_boolexpr(l);
                let r2 = self.from_boolexpr(r);
                self.and(r1, r2)
            }
            &LogicalExpr::Or(ref l, ref r) => {
                let r1 = self.from_boolexpr(l);
                let r2 = self.from_boolexpr(r);
                self.or(r1, r2)
            }
            &LogicalExpr::Not(ref e) => {
                self.from_boolexpr(e).neg()
            },
            &LogicalExpr::Iff(ref l, ref r) => {
                let r1 = self.from_boolexpr(l);
                let r2 = self.from_boolexpr(r);
                self.iff(r1, r2)
            },
            &LogicalExpr::Xor(ref l, ref r) => {
                let r1 = self.from_boolexpr(l);
                let r2 = self.from_boolexpr(r);
                self.xor(r1, r2)
            },
            &LogicalExpr::Ite { ref guard, ref thn, ref els } => {
                let g = self.from_boolexpr(guard);
                let t = self.from_boolexpr(thn);
                let e = self.from_boolexpr(els);
                self.ite(g, t, e)
            },
        }
    }

    /// Compiles a plan into a BDD
    pub fn compile_plan(&mut self, expr: &BddPlan) -> BddPtr {
        match expr {
            &BddPlan::Literal(var, polarity) => self.var(VarLabel::new(var as u64), polarity),
            &BddPlan::And(ref l, ref r) => {
                let r1 = self.compile_plan(&*l);
                let r2 = self.compile_plan(&*r);
                self.and(r1, r2)
            }
            &BddPlan::Or(ref l, ref r) => {
                let r1 = self.compile_plan(&*l);
                let r2 = self.compile_plan(&*r);
                self.or(r1, r2)
            }
            &BddPlan::Iff(ref l, ref r) => {
                let r1 = self.compile_plan(&*l);
                let r2 = self.compile_plan(&*r);
                self.iff(r1, r2)
            }
            &BddPlan::Ite(ref f, ref g, ref h) => {
                let f = self.compile_plan(&*f);
                let g = self.compile_plan(&*g);
                let h = self.compile_plan(&*h);
                self.ite(f, g, h)
            }
            &BddPlan::Not(ref f) => {
                let f = self.compile_plan(&*f);
                self.negate(f)
            }
            &BddPlan::ConstTrue => self.true_ptr(),
            &BddPlan::ConstFalse => self.false_ptr(),
        }
    }

    fn topdown_h(&mut self, cnf: &Cnf, up: &mut UnitPropagate, level: usize) -> BddPtr {
        // check for base case
        if level >= cnf.num_vars() || cnf.is_sat_partial(up.get_assgn()) {
            return self.true_ptr();
        }

        let cur_v = self.get_order().var_at_pos(level);
        // check if this literal is currently set in unit propagation
        match up.get_assgn().get(cur_v) {
            Some(v) => {
                // recurse and uniqify
                let sub = self.topdown_h(cnf, up, level+1);
                if sub == self.false_ptr() {
                    return self.false_ptr();
                }
                let bdd = if v { 
                    BddNode::new(self.false_ptr(), sub, cur_v) 
                } else {
                    BddNode::new(sub, self.false_ptr(), cur_v) 
                };
                self.get_or_insert(bdd)
            },
            None => {
                // recurse on both values of cur_v
                let success = up.decide(Literal::new(cur_v, true));
                let high_bdd = if success {
                    self.topdown_h(cnf, up, level+1)
                } else {
                    self.false_ptr()
                };
                up.backtrack();
                let success = up.decide(Literal::new(cur_v, false));
                let low_bdd = if success {
                    self.topdown_h(cnf, up, level+1)
                } else {
                    self.false_ptr()
                };
                up.backtrack();
                if high_bdd == low_bdd {
                    return high_bdd;
                } else {
                    let bdd = BddNode::new(low_bdd, high_bdd, cur_v);
                    return self.get_or_insert(bdd);
                }
            }
        }
    }

    pub fn from_cnf_topdown(&mut self, cnf: &Cnf) -> BddPtr {
        let mut up = match UnitPropagate::new(cnf) {
            Some(v) => v,
            None => return self.false_ptr()
        };
        self.topdown_h(cnf, &mut up, 0)
    }

    /// Prints the total number of recursive calls executed so far by the BddManager
    /// This is a stable way to track performance 
    pub fn num_recursive_calls(&self) -> usize {
        return self.stats.num_recursive_calls;
    }
}

#[cfg(test)]
mod tests {

    use maplit::*;

    use crate::{
        builder::bdd_builder::{BddManager, BddWmc},
        builder::repr::{builder_bdd::BddPtr}, 
        repr::{var_label::{VarLabel, Literal}, cnf::{Cnf, UnitPropagate}},
    };

    // check that (a \/ b) /\ a === a
    #[test]
    fn simple_equality() {
        let mut man = BddManager::new_default_order(3);
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(1), true);
        let r1 = man.or(v1, v2);
        let r2 = man.and(r1, v1);
        assert!(
            man.eq_bdd(v1, r2),
            "Not eq:\n {}\n{}",
            man.to_string_debug(v1),
            man.to_string_debug(r2)
        );
    }

    #[test]
    fn simple_ite1() {
        let mut man = BddManager::new_default_order(3);
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(1), true);
        let r1 = man.or(v1, v2);
        let r2 = man.ite(r1, v1, BddPtr::false_node());
        assert!(
            man.eq_bdd(v1, r2),
            "Not eq:\n {}\n{}",
            man.to_string_debug(v1),
            man.to_string_debug(r2)
        );
    }

    #[test]
    fn test_newvar() {
        let mut man = BddManager::new_default_order(0);
        let l1 = man.new_var();
        let l2 = man.new_var();
        let v1 = man.var(l1, true);
        let v2 = man.var(l2, true);
        let r1 = man.or(v1, v2);
        let r2 = man.and(r1, v1);
        assert!(
            man.eq_bdd(v1, r2),
            "Not eq:\n {}\n{}",
            man.to_string_debug(v1),
            man.to_string_debug(r2)
        );
    }

    #[test]
    fn test_wmc() {
        let mut man = BddManager::new_default_order(2);
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(1), true);
        let r1 = man.or(v1, v2);
        let weights = hashmap! {VarLabel::new(0) => (2,3),
        VarLabel::new(1) => (5,7)};
        let params = BddWmc::new_with_default(0, 1, weights);
        let wmc = man.wmc(r1, &params);
        assert_eq!(wmc, 50);
    }

    #[test]
    fn test_wmc_smooth() {
        let mut man = BddManager::new_default_order(3);
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(2), true);
        let r1 = man.or(v1, v2);
        let weights = hashmap! {
        VarLabel::new(0) => (2,3),
        VarLabel::new(1) => (5,7),
        VarLabel::new(2) => (11,13)};
        let params = BddWmc::new_with_default(0, 1, weights);
        let wmc = man.wmc(r1, &params);
        assert_eq!(wmc, 1176);
    }

    #[test]
    fn test_wmc_smooth2() {
        let mut man = BddManager::new_default_order(3);
        let r1 = BddPtr::true_node();
        let weights = hashmap! {
        VarLabel::new(0) => (2,3),
        VarLabel::new(1) => (5,7),
        VarLabel::new(2) => (11,13)};
        let params = BddWmc::new_with_default(0, 1, weights);
        let wmc = man.wmc(r1, &params);
        assert_eq!(wmc, 1440);
    }

    #[test]
    fn test_condition() {
        let mut man = BddManager::new_default_order(3);
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(1), true);
        let r1 = man.or(v1, v2);
        let r3 = man.condition(r1, VarLabel::new(1), false);
        assert!(man.eq_bdd(r3, v1));
    }

    #[test]
    fn test_condition_compl() {
        let mut man = BddManager::new_default_order(3);
        let v1 = man.var(VarLabel::new(0), false);
        let v2 = man.var(VarLabel::new(1), false);
        let r1 = man.and(v1, v2);
        let r3 = man.condition(r1, VarLabel::new(1), false);
        assert!(
            man.eq_bdd(r3, v1),
            "Not eq:\nOne: {}\nTwo: {}",
            man.to_string_debug(r3),
            man.to_string_debug(v1)
        );
    }

    #[test]
    fn test_exist() {
        let mut man = BddManager::new_default_order(3);
        // 1 /\ 2 /\ 3
        let v1 = man.var(VarLabel::new(0), true);
        let v2 = man.var(VarLabel::new(1), true);
        let v3 = man.var(VarLabel::new(2), true);
        let a1 = man.and(v1, v2);
        let r1 = man.and(a1, v3);
        let r_expected = man.and(v1, v3);
        let res = man.exists(r1, VarLabel::new(1));
        assert!(
            man.eq_bdd(r_expected, res),
            "Got:\nOne: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(r_expected)
        );
    }

    #[test]
    fn test_exist_compl() {
        let mut man = BddManager::new_default_order(3);
        // 1 /\ 2 /\ 3
        let v1 = man.var(VarLabel::new(0), false);
        let v2 = man.var(VarLabel::new(1), false);
        let v3 = man.var(VarLabel::new(2), false);
        let a1 = man.and(v1, v2);
        let r1 = man.and(a1, v3);
        let r_expected = man.and(v1, v3);
        let res = man.exists(r1, VarLabel::new(1));
        // let res = r1;
        assert!(
            man.eq_bdd(r_expected, res),
            "Got:\n: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(r_expected)
        );
    }

    #[test]
    fn test_compose() {
        let mut man = BddManager::new_default_order(3);
        let v0 = man.var(VarLabel::new(0), true);
        let v1 = man.var(VarLabel::new(1), true);
        let v2 = man.var(VarLabel::new(2), true);
        let v0_and_v1 = man.and(v0, v1);
        let v0_and_v2 = man.and(v0, v2);
        let res = man.compose(v0_and_v1, VarLabel::new(1), v2);
        assert!(
            man.eq_bdd(res, v0_and_v2),
            "\nGot: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(v0_and_v2)
        );
    }

    #[test]
    fn test_compose_2() {
        let mut man = BddManager::new_default_order(4);
        let v0 = man.var(VarLabel::new(0), true);
        let v1 = man.var(VarLabel::new(1), true);
        let v2 = man.var(VarLabel::new(2), true);
        let v3 = man.var(VarLabel::new(3), true);
        let v0_and_v1 = man.and(v0, v1);
        let v2_and_v3 = man.and(v2, v3);
        let v0v2v3 = man.and(v0, v2_and_v3);
        let res = man.compose(v0_and_v1, VarLabel::new(1), v2_and_v3);
        assert!(
            man.eq_bdd(res, v0v2v3),
            "\nGot: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(v0v2v3)
        );
    }

    #[test]
    fn test_compose_3() {
        let mut man = BddManager::new_default_order(4);
        let v0 = man.var(VarLabel::new(0), true);
        let v1 = man.var(VarLabel::new(1), true);
        let v2 = man.var(VarLabel::new(2), true);
        let f = man.ite(v0, man.false_ptr(), v1);
        let res = man.compose(f, VarLabel::new(1), v2);
        let expected = man.ite(v0, man.false_ptr(), v2);
        assert!(
            man.eq_bdd(res, expected),
            "\nGot: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(expected)
        );
    }

    #[test]
    fn test_compose_4() {
        let mut man = BddManager::new_default_order(20);
        let v0 = man.var(VarLabel::new(4), true);
        let v1 = man.var(VarLabel::new(5), true);
        let v2 = man.var(VarLabel::new(6), true);
        let f = man.ite(v1, man.false_ptr(), v2);
        let res = man.compose(f, VarLabel::new(6), v0);
        let expected = man.ite(v1, man.false_ptr(), v0);
        assert!(
            man.eq_bdd(res, expected),
            "\nGot: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(expected)
        );
    }

    #[test]
    fn test_new_var() {
        let mut man = BddManager::new_default_order(0);
        let vlbl1 = man.new_var();
        let vlbl2 = man.new_var();
        let v1 = man.var(vlbl1, false);
        let v2 = man.var(vlbl2, false);
        let r1 = man.and(v1, v2);
        let r3 = man.condition(r1, VarLabel::new(1), false);
        assert!(
            man.eq_bdd(r3, v1),
            "Not eq:\nOne: {}\nTwo: {}",
            man.to_string_debug(r3),
            man.to_string_debug(v1)
        );
    }

    #[test]
    fn circuit1() {
        let mut man = BddManager::new_default_order(3);
        let x = man.var(VarLabel::new(0), false);
        let y = man.var(VarLabel::new(1), true);
        let delta = man.and(x, y);
        let yp = man.var(VarLabel::new(2), true);
        let inner = man.iff(yp, y);
        let conj = man.and(inner, delta);
        let res = man.exists(conj, VarLabel::new(1));

        let expected = man.and(x, yp);
        assert!(
            man.eq_bdd(res, expected),
            "Not eq:\nGot: {}\nExpected: {}",
            man.to_string_debug(res),
            man.to_string_debug(expected)
        );
    }

    #[test]
    fn simple_cond() {
        let mut man = BddManager::new_default_order(3);
        let x = man.var(VarLabel::new(0), true);
        let y = man.var(VarLabel::new(1), false);
        let z = man.var(VarLabel::new(2), false);
        let r1 = man.and(x, y);
        let r2 = man.and(r1, z);
        // now r2 is x /\ !y /\ !z

        let res = man.condition(r2, VarLabel::new(1), true);
        let expected = BddPtr::false_node();
        assert!(
            man.eq_bdd(res, expected),
            "\nOriginal BDD: {}\nNot eq:\nGot: {}\nExpected: {}",
            man.to_string_debug(r2),
            man.to_string_debug(res),
            man.to_string_debug(expected)
        );
    }

    #[test]
    fn wmc_test_2() {
        let mut man = BddManager::new_default_order(4);
        let x = man.var(VarLabel::new(0), true);
        let y = man.var(VarLabel::new(1), true);
        let f1 = man.var(VarLabel::new(2), true);
        let f2 = man.var(VarLabel::new(3), true);
        let map = hashmap! { VarLabel::new(0) => (1.0, 1.0),
        VarLabel::new(1) => (1.0, 1.0),
        VarLabel::new(2) => (0.8, 0.2),
        VarLabel::new(3) => (0.7, 0.3) };
        let wmc = BddWmc::new_with_default(0.0, 1.0, map);
        let iff1 = man.iff(x, f1);
        let iff2 = man.iff(y, f2);
        let obs = man.or(x, y);
        let and1 = man.and(iff1, iff2);
        let f = man.and(and1, obs);
        assert_eq!(man.wmc(f, &wmc), 0.2 * 0.3 + 0.2 * 0.7 + 0.8 * 0.3);
    }

    #[test]
    fn iff_regression() {
        let mut man = BddManager::new_default_order(0);
        let mut ptrvec = Vec::new();
        for i in 0..40 {
            let vlab = man.new_var();
            let flab = man.new_var();
            let vptr = man.var(vlab, true);
            let fptr = man.var(flab, true);
            let sent = man.iff(vptr, fptr);
            ptrvec.push(sent);
        }
        let resptr = ptrvec
            .iter()
            .fold(man.true_ptr(), |acc, x| man.and(acc, *x));
        assert!(true);
    }

    #[test]
    fn test_topdown_1() {
        let clauses = vec![vec![Literal::new(VarLabel::new(0), true), Literal::new(VarLabel::new(1), true)]];
        let cnf = Cnf::new(clauses);
        let mut mgr = BddManager::new_default_order(2);
        let c1 = mgr.from_cnf(&cnf);
        let c2 = mgr.from_cnf_topdown(&cnf);
        assert_eq!(c1, c2, "BDD not equal: got {}, expected {}", mgr.to_string_debug(c2), mgr.to_string_debug(c1));
    }

    #[test]
    fn test_topdown_2() {
        let clauses = vec![vec![Literal::new(VarLabel::new(0), false), Literal::new(VarLabel::new(1), false)]];
        let cnf = Cnf::new(clauses);
        let mut mgr = BddManager::new_default_order(2);
        let c1 = mgr.from_cnf(&cnf);
        let c2 = mgr.from_cnf_topdown(&cnf);
        assert_eq!(c1, c2, "BDD not equal: got {}, expected {}", mgr.to_string_debug(c2), mgr.to_string_debug(c1));
    }

    #[test]
    fn test_topdown_3() {
        let clauses = vec![vec![Literal::new(VarLabel::new(1), true), Literal::new(VarLabel::new(3), true)],
                           vec![Literal::new(VarLabel::new(3), false), Literal::new(VarLabel::new(2), true), Literal::new(VarLabel::new(4), true)]];
        let cnf = Cnf::new(clauses);
        let mut mgr = BddManager::new_default_order(cnf.num_vars());
        let c1 = mgr.from_cnf(&cnf);
        let c2 = mgr.from_cnf_topdown(&cnf);
        assert_eq!(c1, c2, "BDD not equal: got {}, expected {}", mgr.to_string_debug(c2), mgr.to_string_debug(c1));
    }

}
