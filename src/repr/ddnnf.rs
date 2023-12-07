//! Implementing of a generic decision decomposable deterministic negation normal form
//! (d-DNNF) pointer type
use crate::{
    repr::{
        var_label::{VarLabel, VarSet},
        WmcParams
    },
    util::semirings::{BooleanSemiring, FiniteField, Semiring},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::{collections::HashMap, fmt::Debug, hash::Hash};

/// creates a weighting that can be used for semantically hashing a DDNNF node
/// the constant `P` denotes the size of the field over which the semantic hash will
/// be computed. For more info, see <https://tr.inf.unibe.ch/pdf/iam-06-001.pdf>
pub fn create_semantic_hash_map<const P: u128>(num_vars: usize) -> WmcParams<FiniteField<P>> {
    let vars: Vec<VarLabel> = (0..num_vars).map(VarLabel::new_usize).collect();

    // theoretical guarantee from paper; need to verify more!
    // in "theory", this should be a 0.1% fail rate in one-shot for a BDD.
    // not sure how to extend to SDDs (and this does not happen in practice)
    assert!(((vars.len() * 1000) as u128) < P);

    // seed the RNG deterministically for reproducible weights across
    // different calls to `create_semantic_hash_map`
    let mut rng = ChaCha8Rng::seed_from_u64(101249);
    // let mut rng = ChaCha8Rng::from_entropy();

    let value_range: Vec<(FiniteField<P>, FiniteField<P>)> = (0..vars.len() as u128)
        .map(|_| {
            let h = FiniteField::new(rng.gen_range(2..P));
            let l = FiniteField::new(P - h.value() + 1);
            (l, h)
        })
        .collect();

    let mut map = HashMap::new();

    for (&var, &value) in vars.iter().zip(value_range.iter()) {
        map.insert(var, value);
    }

    WmcParams::new(map)
}

#[derive(Debug)]    
pub enum GradData<T> {
    V(VarLabel, bool),
    True,
    False,
    Gr(Vec<T>),
}
/// A base d-DNNF type
pub enum DDNNF<T> {
    /// contains the cached values for the children, and the VarSet that
    /// contains the set of decision variables that this Or node was made with
    Or(T, T, VarSet, Vec<GradData<T>>),
    And(T, T, Vec<GradData<T>>),
    Lit(VarLabel, bool),
    True,
    False,
}

pub trait DDNNFPtr<'a>: Clone + Debug + PartialEq + Eq + Hash + Copy {
    /// performs a memoized bottom-up pass with aggregating function `f` calls
    fn fold<T: Semiring, F: Fn(DDNNF<T>) -> T>(&self, f: F) -> T
    where
        T: 'static;

    /// Unsmoothed weighted-model count
    fn unsmoothed_wmc<T: Semiring + std::ops::Add<Output = T> + std::ops::Mul<Output = T>>(
        &self,
        params: &WmcParams<T>,
    ) -> T
    where
        T: 'static,
    {
        println!("START_COUNT");
        self.fold(|ddnnf| {
            use DDNNF::*;
            match ddnnf {
                Or(l, r, _,_) => {
                    println!("or l: {:?}, r: {:?}", l, r);
                    l + r},
                And(l, r, _) => {
                    println!("and l: {:?}, r: {:?}", l, r);
                    l * r},
                True => {
                    println!("TRUE 1");
                    params.one
                },
                False => {
                    println!("FALSE 0");
                    params.zero
                }
                Lit(lbl, polarity) => {
                    let (low_w, high_w) = params.var_weight(lbl);
                    // println!("lit lbl: {:?}, polarity: {:?}", lbl, polarity);
                    if polarity {
                        println!("low_w: {:?}, HIGH_W: {:?}", low_w, high_w);
                        *high_w
                    } else {
                        println!("LOW_W: {:?}, high_w: {:?}", low_w, high_w);
                        *low_w
                    }
                }
            }
        })
    }


    fn fold_gr<T: Semiring, F: Fn(DDNNF<T>) -> T, G: Fn(DDNNF<T>) -> Vec<T>>(&self, f: F, g :G) -> (T, Vec<T>)
    where
        T: 'static;


    /// Unsmoothed weighted-model count
    fn unsmoothed_wmc_gr<T: Semiring + std::ops::Add<Output = T> + std::ops::Mul<Output = T> + std::ops::Neg<Output = T>>(
        &self,
        params: &WmcParams<T>,
    ) -> (T, Vec<T>)
    where
        T: 'static,
    {

        self.fold_gr(|ddnnf| {
            use DDNNF::*;
            let verbose = false;
            match ddnnf {
                Or(l, r, _,_) => {
                    if verbose{
                        println!("or l: {:?}, r: {:?}", l, r);
                    }
                    l + r},
                And(l, r, _) => {
                    if verbose{
                        println!("and l: {:?}, r: {:?}", l, r);
                    }
                    l * r},
                True => {
                    if verbose{
                        println!("TRUE 1");
                    }
                    params.one
                },
                False => {
                    if verbose{
                        println!("FALSE 0");
                    }
                    params.zero
                }
                Lit(lbl, polarity) => {
                    let (low_w, high_w) = params.var_weight(lbl);
                    // println!("lit lbl: {:?}, polarity: {:?}", lbl, polarity);
                    if polarity {
                        if verbose {
                            println!("low_w: {:?}, HIGH_W: {:?}", low_w, high_w);
                        }
                        *high_w
                    } else {
                        if verbose {
                            println!("LOW_W: {:?}, high_w: {:?}", low_w, high_w);
                        }
                        *low_w
                    }
                }
            }
        }, |ddnnf| {
            use DDNNF::*;
            let verbose = false;
            let special = false;
            match ddnnf {
                Or(l, r, _, gr) => {
                    // for every lbl i in v, get grdaient vector then sum
                    let mut sum = vec![params.zero; gr.len()];
                    // println!("v: {:?}", gr);
                    for i in gr.iter() {
                        match i {
                            GradData::V(x, true)=> {
                                let mut grad = params.var_gradient(*x);
                                for j in 0..grad.len() {
                                    sum[j] = sum[j] + grad[j];
                                }
                            },
                            GradData::V(x, false)=> {
                                let mut grad = params.var_gradient(*x);
                                for j in 0..grad.len() {
                                    sum[j] = sum[j] + grad[j].neg();
                                }
                            },
                            _ => (),
                            
                        } 
                    }
                    // return vector sum
                    if verbose{
                        println!("orSUM sum: {:?}", sum);
                    }
                    
                    sum
                }
                And(l, r, gr) => {
                    // println!("gr: {:?}", gr);
                    if verbose || special {
                        println!("and l: {:?}, r: {:?}", l, r);
                    }
                    // for every lbl i in v, get grdaient vector then sum
                    let mut sum = vec![params.zero; gr.len()];
                    // println!("sum: {:?}", sum);
                    let mult = vec![r, l];
                    for i in 0..gr.len() {
                        match &gr[i] {
                            GradData::V(x, true)=> {
                                // let iu = x.value() as usize;
                                let mut grad : &mut Vec<T> = &mut params.var_gradient(*x).clone();
                                for j in 0..grad.len() {
                                    grad[j] =  mult[i]*grad[j];
                                }
                                if verbose || special {
                                    println!("ANDgrad inner : {:?}", grad);
                                }
                                for j in 0..grad.len() {
                                    sum[j] =  sum[j] + grad[j];
                                }
                            },
                            GradData::V(x, false)=> {
                                // let iu = x.value() as usize;
                                let mut grad : &mut Vec<T> = &mut params.var_gradient(*x).clone();

                                // println!("negating");
                                for j in 0..grad.len() {
                                    grad[j] =  grad[j].neg();
                                }
                                
                                for j in 0..grad.len() {
                                    grad[j] =  mult[i]*grad[j];
                                }
                                if verbose || special {
                                    println!("ANDgrad inner : {:?}", grad);
                                }
                                for j in 0..grad.len() {
                                    sum[j] =  sum[j] + grad[j];
                                }
                            },
                            GradData::Gr(x) => { 
                                let y = x.clone();
                                for j in 0..sum.len() {
                                    sum[j] =  sum[j] + y[j];
                                }
                            },
                            _ => {
                                for j in 0..gr.len() {
                                    sum[j] =  sum[j] + params.zero;
                                }
                            }
                            
                        }
                    }
                    // return vector sum
                    if verbose || special{
                        println!("andSUM sum: {:?}", sum);
                    }
                    sum
                }
                True => {
                    let mut grad = vec![params.zero; params.grad_len()];
                    for i in 0..grad.len() {
                        grad[i] = params.zero;
                    }
                    if verbose{
                        println!("trueSUM sum: {:?}", grad);
                    }
                    grad
                },
                False => {
                    let mut grad = vec![params.zero; params.grad_len()];
                    for i in 0..grad.len() {
                        grad[i] = params.zero;
                    }
                    if verbose{
                        println!("falseSUM sum: {:?}", grad);
                    }
                    grad
                }
                Lit(lbl, polarity) => {
                    let (low_w, high_w) = params.var_weight(lbl);
                    // println!("lit lbl: {:?}, polarity: {:?}", lbl, polarity);
                    if polarity {
                        let grad = params.var_gradient(lbl).to_vec();
                        if verbose{
                            println!("GRAD HIGH_W: {:?}", grad);
                        }
                        grad
                    } else {
                        // println!("LOW_W: {:?}, high_w: {:?}", low_w, high_w);
                        // multiplt by -1 each element
                        let mut grad = params.var_gradient(lbl).clone();
                        for i in 0..grad.len() {
                            grad[i] = grad[i].neg();
                        }
                        if verbose{
                            println!("GRAD low_W: {:?}", grad);
                        }
                        grad
                    }
                }
            }
        })
    }

    // /// Unsmoothed weighted-model count with gradients
    // fn unsmoothed_wmc<T: Semiring + std::ops::Add<Output = T> + std::ops::Mul<Output = T>>(
    //     &self,
    //     params: &WmcParams<T>,
    // ) -> (T, Vec<T>)
    // where
    //     T: 'static,
    // {
    //     self.fold(|ddnnf| {
    //         use DDNNF::*;
    //         match ddnnf {
    //             Or(l, r, _) => l + r,
    //             And(l, r) => l * r,
    //             True => params.one,
    //             False => params.zero,
    //             Lit(lbl, polarity) => {
    //                 let (low_w, high_w) = params.var_weight(lbl);
    //                 if polarity {
    //                     *high_w
    //                 } else {
    //                     *low_w
    //                 }
    //             }
    //         }
    //     })
    // }

    fn evaluate(&self, instantations: &[bool]) -> bool {
        self.unsmoothed_wmc(&WmcParams::new(HashMap::from_iter(
            instantations.iter().enumerate().map(|(index, polarity)| {
                (
                    VarLabel::new(index as u64),
                    (BooleanSemiring(!polarity), BooleanSemiring(*polarity)),
                )
            }),
        )))
        .0
    }

    /// compute the semantic hash for this pointer
    fn semantic_hash<const P: u128>(&self, map: &WmcParams<FiniteField<P>>) -> FiniteField<P> {
        self.unsmoothed_wmc(map)
    }

    /// Negate the pointer
    fn neg(&self) -> Self;
    /// Generate a pointer to the false constant
    fn false_ptr() -> Self;
    /// Generate a pointer to the true constant
    fn true_ptr() -> Self;
    /// True if `self` is a true constant, false otherwise
    fn is_true(&self) -> bool;
    /// True if `self` is a false constant, false otherwise
    fn is_false(&self) -> bool;
    /// True if `self` is a negated pointer, false otherwise
    fn is_neg(&self) -> bool;

    /// count the number of nodes in this representation
    fn count_nodes(&self) -> usize;
}
