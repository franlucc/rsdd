#![allow(unused)]
use rsdd::builder::sdd::SddBuilder;
use rsdd::builder::bdd::RobddBuilder;
use rsdd::builder::cache::AllIteTable;
use rsdd::builder::sdd::{CompressionSddBuilder, SemanticSddBuilder};
use rsdd::builder::BottomUpBuilder;
use rsdd::constants::primes;
use rsdd::repr::BddPtr;
use rsdd::repr::Cnf;
use rsdd::repr::DTree;
use rsdd::repr::SddPtr;
use rsdd::repr::VTree;
use rsdd::repr::VarOrder;
use rsdd::repr::WmcParams;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use rand::SeedableRng;
use rsdd::repr::{create_semantic_hash_map, DDNNFPtr};
use rsdd::repr::{VarLabel, Literal};
use rsdd::util::semirings::FiniteField;
use std::collections::HashMap;
use rsdd::util::semirings::RealSemiring;

// #[test]
// fn my_test_sdd_wmc_eq_even_split(){
//     let mut rng = ChaCha8Rng::seed_from_u64(101249);
    
//     let clauses = [
//         vec![
//             Literal::new(VarLabel::new(2), true),
//             Literal::new(VarLabel::new(3), true),
//         ]
//         // , vec![Literal::new(VarLabel::new(8), true)]
//     ];
//     println!("clauses: {:#?}\n\n", clauses);
//     let cnf = Cnf::new(&clauses);
//     println!("cnf: {}\n\n", cnf);
//     println!("cnf_num: {}\n\n", cnf.num_vars());
//     // let cnf = Cnf::from_dimacs(C1_B);
//     let vars: Vec<VarLabel> = (0..cnf.num_vars()).map(VarLabel::new_usize).collect();

//     let value_range : Vec<(FiniteField<{primes::U32_SMALL}>, FiniteField<{primes::U32_SMALL}>)>= (0..vars.len() as u128)
//         .map(|_| {
//             let h = FiniteField::new(rng.gen_range(2..10));
//             let l = FiniteField::new(10 - h.value());
//             (l, h)
//         })
//         .collect();

//     let mut map = HashMap::new();

//     for (&var, &value) in vars.iter().zip(value_range.iter()) {
//         map.insert(var, value);
//     }

//    let weight_map = WmcParams::new(map);

//    println!("weight_map: {:#?}\n\n", weight_map);
//    let order : Vec<VarLabel> = (0..cnf.num_vars()).map(|x| VarLabel::new(x as u64)).collect();
//    println!("order: {:#?}\n\n", order);
//    let builder = CompressionSddBuilder::new(VTree::even_split(&order, 3));
//    let cnf_sdd = builder.compile_cnf(&cnf);
//    println!("sdd: {}\n\n", builder.print_sdd(cnf_sdd));
// //    let sdd_res = cnf_sdd.semantic_hash(&weight_map);
//    let sdd_res = cnf_sdd.unsmoothed_wmc(&weight_map);


//     let bdd_builder = RobddBuilder::<AllIteTable<BddPtr>>::new_with_linear_order(cnf.num_vars());
//     let cnf_bdd = bdd_builder.compile_cnf(&cnf);
//     let bdd_res = cnf_bdd.semantic_hash( &weight_map);
//     println!("cnf: {}\n\n", cnf);
//     println!("bdd_res: {}\n\n", bdd_res);
//     println!("sdd_res: {}\n\n", sdd_res);
//     println!("DONE");
//     assert_ne!(bdd_res, sdd_res);
// }

#[test]
fn is_canonical_simple_demorgan() {
    let mut rng = ChaCha8Rng::seed_from_u64(101);

    let vars = [
        VarLabel::new(0),
        VarLabel::new(1),
        VarLabel::new(2),
    ];

    use rsdd::repr::VTree;
    let builder = CompressionSddBuilder::new(VTree::even_split(
        &vars,
        1,
    ));

    let x = SddPtr::Var(VarLabel::new(0), true);
    let y = SddPtr::Var(VarLabel::new(1), true);
    let z = SddPtr::Var(VarLabel::new(2), true);
    let res1 = builder.and(x, y);
    let res = builder.or(res1, z);
    println!("res: {}\n\n", builder.print_sdd(res));
    println!("res: {:#?}\n\n", res.count_nodes());
    // let expected = builder.and(x.neg(), y.neg());

    let len_vars = vars.len();

    // let value_range : Vec<(FiniteField<{primes::U32_SMALL}>, FiniteField<{primes::U32_SMALL}>)>= (0..len_vars as u128)
    // .map(|_| {
    //     let h = FiniteField::new(rng.gen_range(1..10));
    //     let l = FiniteField::new(10 - h.value());
    //     (l, h)
    // })
    // .collect();

    // let mut map = HashMap::new();

    let float_weights : Vec<(f32, f32)> = vec![(0.2, 0.8), (0.9, 0.1), (0.3, 0.7), (0.4, 0.6), (0.5, 0.5)];

    let weight_hash : HashMap<VarLabel, (RealSemiring, RealSemiring)> = HashMap::from_iter(
        (0..len_vars as u64)
            .map(|i| (VarLabel::new(i), (RealSemiring(float_weights[i as usize].1 as f64), RealSemiring(float_weights[i as usize].0 as f64))))
    );

    // for (&var, &value) in vars.iter().zip(value_range.iter()) {
    //     map.insert(var, value);
    // }
    let gr_hash  : HashMap<VarLabel, Vec<RealSemiring>> = HashMap::from_iter({
        let mut tmp = HashMap::new();
        tmp.insert(VarLabel::new(0), vec![RealSemiring(1.0), RealSemiring(0.0)]);
        tmp.insert(VarLabel::new(1), vec![RealSemiring(0.0), RealSemiring(1.0)]);
        tmp.insert(VarLabel::new(2), vec![RealSemiring(0.0), RealSemiring(0.0)]);
        tmp
    
    });

   let weight_map = WmcParams::<RealSemiring>::new_with_gr(weight_hash, gr_hash);
   

   println!("weight_map: {:#?}\n\n", weight_map);
   let order : Vec<VarLabel> = (0..len_vars).map(|x| VarLabel::new(x as u64)).collect();
   println!("order: {:#?}\n\n", order);

//    let sdd_res = cnf_sdd.semantic_hash(&weight_map);
    let sdd_res = res.unsmoothed_wmc_gr(&weight_map);
    println!("sdd_res: {:#?}\n\n", sdd_res);
    // let bdd_res = expected.unsmoothed_wmc(&weight_map);
    // println!("bdd_res: {}\n\n", bdd_res);

    println!("DONE");
    // assert!(expected.is_canonical());
    assert!(!res.is_canonical());
}