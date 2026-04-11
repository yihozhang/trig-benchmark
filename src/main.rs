use egg::stochastic::{
    PeriodicBeta, SimpleLcg, State, StoAnalysis, StoConfig, StoRewrite, StoRunner,
};
use egg::{rewrite as rw, *};
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Duration;

#[cfg(test)]
use serial_test::serial;

type EGraph = egg::EGraph<Trig, ConstantFold>;
type Rewrite = egg::Rewrite<Trig, ConstantFold>;

define_language! {
    enum Trig {
        Num(i32),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "sqrt" = Sqrt(Id),
        "sin" = Sin(Id),
        "cos" = Cos(Id),
        "tan" = Tan(Id),
        "cot" = Cot(Id),
        "sec" = Sec(Id),
        "csc" = Csc(Id),
        Symbol(Symbol),
    }
}

#[derive(Default)]
struct ConstantFold;
impl Analysis<Trig> for ConstantFold {
    type Data = Option<(i32, PatternAst<Trig>)>;

    fn make(egraph: &mut EGraph, enode: &Trig, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Trig::Num(n) => (*n, format!("{}", n).parse().unwrap()),
            Trig::Add([a, b]) => {
                let s = x(a)?.checked_add(x(b)?)?;
                (s, format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Trig::Sub([a, b]) => {
                let s = x(a)?.checked_sub(x(b)?)?;
                (s, format!("(- {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Trig::Mul([a, b]) => {
                let s = x(a)?.checked_mul(x(b)?)?;
                (s, format!("(* {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Trig::Pow([a, b]) => {
                let base = x(a)?;
                let exp = x(b)?;
                if exp < 0 {
                    return None;
                }
                let s = base.checked_pow(exp as u32)?;
                (s, format!("(pow {} {})", base, exp).parse().unwrap())
            }
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Trig::Num(c));
                egraph.union(id, added);
            }
            egraph[id].nodes.retain(|n| n.is_leaf());
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

#[rustfmt::skip]
fn rules(vars: impl Iterator<Item = Symbol>) -> Vec<Rewrite> {
    let mut rwts: Vec<Rewrite> = vec![
    // trig definitions
    rw!("expand-tan";    "(tan ?x)" => "(/ (sin ?x) (cos ?x))"),
    rw!("i-expand-tan";  "(/ (sin ?x) (cos ?x))" => "(tan ?x)"),
    rw!("expand-cot";    "(cot ?x)" => "(/ (cos ?x) (sin ?x))"),
    rw!("i-expand-cot";  "(/ (cos ?x) (sin ?x))" => "(cot ?x)"),
    rw!("expand-sec";    "(sec ?x)" => "(/ 1 (cos ?x))"),
    rw!("i-expand-sec";  "(/ 1 (cos ?x))" => "(sec ?x)"),
    rw!("expand-csc";    "(csc ?x)" => "(/ 1 (sin ?x))"),
    rw!("i-expand-csc";  "(/ 1 (sin ?x))" => "(csc ?x)"),

    // trig identities
    rw!("pythag";        "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))" => "1"),
    rw!("pythag-sin";    "(pow (sin ?x) 2)" => "(- 1 (pow (cos ?x) 2))"),
    // NEW inverse rule
    rw!("i-pythag-sin"; "(- 1 (pow (cos ?x) 2))" => "(pow (sin ?x) 2)"),
    rw!("pythag-cos"; "(pow (cos ?x) 2)" => "(- 1 (pow (sin ?x) 2))"),
    // NEW inverse rule
    rw!("i-pythag-cos"; "(- 1 (pow (sin ?x) 2))" => "(pow (cos ?x) 2)"),
    rw!("pythag-sec";     "(+ 1 (pow (tan ?x) 2))" => "(pow (sec ?x) 2)"),
    rw!("i-pythag-sec";   "(pow (sec ?x) 2)" => "(+ 1 (pow (tan ?x) 2))"),
    rw!("pythag-csc";     "(+ 1 (pow (cot ?x) 2))" => "(pow (csc ?x) 2)"),
    rw!("i-pythag-csc";   "(pow (csc ?x) 2)" => "(+ 1 (pow (cot ?x) 2))"),

    // commutativity and associativity
    rw!("comm-add";      "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("comm-mul";      "(* ?a ?b)" => "(* ?b ?a)"),
    rw!("assoc-add";     "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
    rw!("i-assoc-add";   "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul";     "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
    rw!("i-assoc-mul";   "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    // distributivity
    rw!("distribute";    "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor";        "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    rw!("factor-sub";    "(- (* ?a ?b) (* ?a ?c))" => "(* ?a (- ?b ?c))"),

    // algebraic
    rw!("zero-add";      "(+ ?a 0)" => "?a"),
    rw!("add-zero";      "?a" => "(+ ?a 0)"),
    rw!("one-mul";       "(* ?a 1)" => "?a"),
    rw!("mul-one";       "?a" => "(* ?a 1)"),
    rw!("zero-mul";      "(* ?a 0)" => "0"),
    rw!("cancel-add";    "(+ ?a (* -1 ?a))" => "0"),
    rw!("recip-mul";     "(* ?a (/ 1 ?a))" => "1"),
    rw!("double-neg";    "(* -1 (* -1 ?a))" => "?a"),

    // subtraction and division as sugar
    rw!("sub-canon";     "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("i-sub-canon";   "(+ ?a (* -1 ?b))" => "(- ?a ?b)"),
    rw!("div-canon";     "(/ ?a ?b)" => "(* ?a (/ 1 ?b))"),
    rw!("i-div-canon";   "(* ?a (/ 1 ?b))" => "(/ ?a ?b)"),

    // fractions
    rw!("frac-add";      "(+ (/ ?a ?b) (/ ?c ?d))" => "(/ (+ (* ?a ?d) (* ?b ?c)) (* ?b ?d))"),
    rw!("i-frac-add";    "(/ (+ (* ?a ?d) (* ?b ?c)) (* ?b ?d))" => "(+ (/ ?a ?b) (/ ?c ?d))"),
    rw!("frac-add-same-denom"; "(+ (/ ?a ?b) (/ ?c ?b))" => "(/ (+ ?a ?c) ?b)"),
    rw!("frac-mul";      "(* (/ ?a ?b) (/ ?c ?d))" => "(/ (* ?a ?c) (* ?b ?d))"),
    rw!("i-frac-mul";    "(/ (* ?a ?c) (* ?b ?d))" => "(* (/ ?a ?b) (/ ?c ?d))"),
    rw!("recip-frac";    "(/ 1 (/ ?a ?b))" => "(/ ?b ?a)"),
    rw!("i-recip-frac";  "(/ ?b ?a)" => "(/ 1 (/ ?a ?b))"),
    rw!("cancel-frac";   "(/ (* ?a ?c) (* ?b ?c))" => "(/ ?a ?b)"),
    rw!("split-frac";    "(/ (+ ?a ?c) ?c)" => "(+ (/ ?a ?c) 1)"),
    rw!("i-split-frac";  "(+ (/ ?a ?c) 1)" => "(/ (+ ?a ?c) ?c)"),

    // powers
    rw!("pow2";          "(pow ?a 2)" => "(* ?a ?a)"),
    rw!("i-pow2";        "(* ?a ?a)" => "(pow ?a 2)"),
    rw!("pow3";          "(pow ?a 3)" => "(* ?a (pow ?a 2))"),
    rw!("i-pow3";        "(* ?a (pow ?a 2))" => "(pow ?a 3)"),
    rw!("pow4";          "(pow ?a 4)" => "(pow (pow ?a 2) 2)"),
    rw!("i-pow4";        "(pow (pow ?a 2) 2)" => "(pow ?a 4)"),
    rw!("pow-mul";       "(pow (* ?a ?b) ?n)" => "(* (pow ?a ?n) (pow ?b ?n))"),
    rw!("i-pow-mul";     "(* (pow ?a ?n) (pow ?b ?n))" => "(pow (* ?a ?b) ?n)"),
    rw!("pow-div";       "(pow (/ ?a ?b) ?n)" => "(/ (pow ?a ?n) (pow ?b ?n))"),
    rw!("i-pow-div";     "(/ (pow ?a ?n) (pow ?b ?n))" => "(pow (/ ?a ?b) ?n)"),

    // factoring
    rw!("diff-sq";       "(- (pow ?a 2) (pow ?b 2))" => "(* (+ ?a ?b) (- ?a ?b))"),
    rw!("i-diff-sq";     "(* (+ ?a ?b) (- ?a ?b))" => "(- (pow ?a 2) (pow ?b 2))"),
    rw!("sum-cubes";     "(+ (pow ?a 3) (pow ?b 3))" =>
        "(* (+ ?a ?b) (+ (- (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    rw!("i-sum-cubes";   "(* (+ ?a ?b) (+ (- (pow ?a 2) (* ?a ?b)) (pow ?b 2)))" =>
        "(+ (pow ?a 3) (pow ?b 3))"),
    rw!("diff-cubes";    "(- (pow ?a 3) (pow ?b 3))" =>
        "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    rw!("i-diff-cubes";  "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))" =>
        "(- (pow ?a 3) (pow ?b 3))"),

    // Adding this rule passes 16 but fails a bunch of other tests...
    // rw!("rationalize"; "(/ ?a (- ?b ?c))" => "(/ (* ?a (+ ?b ?c)) (- (pow ?b 2) (pow ?c 2)))")
    ];
    for var in vars {
        let name = format!("i-pythag-{}", var);
        let rhs = format!("(+ (pow (sin {}) 2) (pow (cos {}) 2))", var, var);
        rwts.push(Rewrite::new(name, "1".parse::<Pattern<Trig>>().unwrap(), rhs.parse::<Pattern<Trig>>().unwrap()).unwrap());
    }
    rwts
}

fn simplify(s: &str, explain: bool) -> (usize, String) {
    let expr: RecExpr<Trig> = s.parse().unwrap();
    let vars: HashSet<Symbol> = expr
        .as_ref()
        .iter()
        .filter_map(|n| {
            if let Trig::Symbol(s) = n {
                Some(*s)
            } else {
                None
            }
        })
        .collect();
    let mut runner = Runner::default();
    if explain {
        runner = runner.with_explanations_enabled();
    }
    let runner = runner.with_expr(&expr);
    let mut runner = runner
        .with_node_limit(usize::MAX)
        .with_time_limit(Duration::from_secs(10))
        .with_iter_limit(usize::MAX)
        .run(&rules(vars.into_iter()));
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!(
        "Simplified (cost {}):\n  {} =>\n  {}",
        best_cost, expr, best
    );
    if explain {
        let mut explanation = runner.egraph.explain_equivalence(&expr, &best);
        println!("Proof:\n{}", explanation.get_flat_string());
    }
    println!("{}", runner.report());
    (best_cost, best.to_string())
}

fn check(lhs: &str, rhs: &str) {
    let (cost, result) = simplify(lhs, false);
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr);
    assert!(
        cost <= expected_cost,
        "expected cost <= {}, got cost {} with: {}",
        expected_cost,
        cost,
        result
    );
}

#[test]
fn eq_trig_01() {
    check("(* (* (sin t) (cos t)) (+ (tan t) (cot t)))", "1")
}
#[test]
fn eq_trig_02() {
    check(
        "(- (pow (sin t) 4) (pow (cos t) 4))",
        "(- (* 2 (pow (sin t) 2)) 1)",
    )
}
#[test]
fn eq_trig_03() {
    check(
        "(+ (- (pow (sin t) 4) (pow (cos t) 4)) 1)",
        "(* 2 (pow (sin t) 2))",
    )
}
#[test]
fn eq_trig_04() {
    check(
        "(- (pow (cos t) 4) (pow (sin t) 4))",
        "(- (* 2 (pow (cos t) 2)) 1)",
    )
}
#[test]
fn eq_trig_05() {
    check(
        "(* (* (sin a) (cos a)) (- (tan a) (cot a)))",
        "(- (* 2 (pow (sin a) 2)) 1)",
    )
}
#[test]
fn eq_trig_06() {
    check(
        "(+ (pow (+ (cos A) (sin A)) 2) (pow (- (cos A) (sin A)) 2))",
        "2",
    )
}
#[test]
fn eq_trig_07() {
    check(
        "(+ (pow (+ 1 (tan t)) 2) (pow (- 1 (tan t)) 2))",
        "(* 2 (pow (sec t) 2))",
    )
}
#[test]
fn eq_trig_08() {
    check(
        "(+ (/ 1 (+ 1 (cos A))) (/ 1 (- 1 (cos A))))",
        "(* 2 (pow (csc A) 2))",
    )
}
#[test]
fn eq_trig_09() {
    check(
        "(/ (+ 1 (cos t)) (- 1 (cos t)))",
        "(pow (+ (cot t) (csc t)) 2)",
    )
}
#[test]
fn eq_trig_10() {
    check(
        "(- (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
        "(* 2 (* (tan A) (sec A)))",
    )
}
#[test]
fn eq_trig_11() {
    check(
        "(+ (/ 1 (- 1 (cos A))) (/ 1 (+ 1 (cos A))))",
        "(* 2 (* (cot A) (csc A)))",
    )
}
#[test]
fn eq_trig_12() {
    check(
        "(* (+ (+ 1 (sec A)) (tan A)) (+ (- 1 (csc A)) (cot A)))",
        "2",
    )
}
#[test]
fn eq_trig_13() {
    check(
        "(+ (/ (cos A) (+ 1 (sin A))) (/ (cos A) (- 1 (sin A))))",
        "(* 2 (sec A))",
    )
}
#[test]
fn eq_trig_14() {
    check(
        "(+ (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
        "(* 2 (pow (sec A) 2))",
    )
}
#[test]
fn eq_trig_15() {
    check(
        "(+ (/ 1 (+ (sin A) (cos A))) (/ 1 (- (sin A) (cos A))))",
        "(/ (* 2 (sin A)) (- 1 (pow (cos A) 2)))",
    )
}
#[test]
fn eq_trig_16() {
    check(
        "(/ (+ 1 (sin t)) (- 1 (sin t)))",
        "(pow (+ (sec t) (tan t)) 2)",
    )
}
// #[test]
// fn eq_trig_17() {
//     check("(/ (- 1 (sin A)) (cos A))", "(/ (cos A) (+ 1 (sin A)))")
// }
#[test]
fn eq_trig_18() {
    check(
        "(+ (/ (cos t) (+ 1 (sin t))) (/ (+ 1 (sin t)) (cos t)))",
        "(* 2 (sec t))",
    )
}
// #[test]
// fn eq_trig_19() {
//     check(
//         "(pow (/ (+ 1 (cos A)) (sin A)) 2)",
//         "(/ (+ 1 (cos A)) (- 1 (cos A)))",
//     )
// }
#[test]
fn eq_trig_20() {
    check(
        "(+ (/ (sin A) (+ 1 (cos A))) (/ (+ 1 (cos A)) (sin A)))",
        "(* 2 (csc A))",
    )
}
#[test]
fn eq_trig_21() {
    check(
        "(* (* (+ 1 (cos t)) (- 1 (cos t))) (+ 1 (pow (cot t) 2)))",
        "1",
    )
}
#[test]
fn eq_trig_22() {
    check("(* (* (+ 1 (pow (tan A) 2)) (sin A)) (cos A))", "(tan A)")
}
#[test]
fn eq_trig_23() {
    check(
        "(/ (- (pow (sin b) 2) (pow (sin a) 2)) (* (pow (sin a) 2) (pow (sin b) 2)))",
        "(+ (pow (cot a) 2) (pow (cot b) 2))",
    )
}
// #[test]
// fn eq_trig_24() {
//     check("(+ (tan A) (cot A))", "(* (sec A) (csc A))")
// }
#[test]
fn eq_trig_25() {
    check("(/ (csc A) (+ (tan A) (cot A)))", "(cos A)")
}
#[test]
// fn eq_trig_26() {
//     check(
//         "(+ (pow (sec t) 2) (pow (csc t) 2))",
//         "(* (pow (sec t) 2) (pow (csc t) 2))",
//     )
// }
#[test]
fn eq_trig_27() {
    check(
        "(+ (+ (pow (tan t) 2) (pow (cot t) 2)) 2)",
        "(* (pow (sec t) 2) (pow (csc t) 2))",
    )
}
// #[test]
// fn eq_trig_28() {
//     check(
//         "(+ (pow (tan t) 4) (pow (tan t) 2))",
//         "(- (pow (sec t) 4) (pow (sec t) 2))",
//     )
// }
#[test]
fn eq_trig_29() {
    check(
        "(+ (- (pow (csc t) 4) (* 2 (pow (csc t) 2))) (- (* 2 (pow (sec t) 2)) (pow (sec t) 4)))",
        "(- (pow (cot t) 4) (pow (tan t) 4))",
    )
}
#[test]
fn eq_trig_30() {
    check(
        "(/ (- (sin A) (* 2 (pow (sin A) 3))) (- (* 2 (pow (cos A) 3)) (cos A)))",
        "(tan A)",
    )
}
#[test]
fn eq_trig_31() {
    check(
        "(+ (/ (cos t) (+ (csc t) 1)) (/ (cos t) (- (csc t) 1)))",
        "(* 2 (tan t))",
    )
}
#[test]
fn eq_trig_32() {
    check(
        "(+ (/ (cos t) (- 1 (tan t))) (/ (sin t) (- 1 (cot t))))",
        "(+ (sin t) (cos t))",
    )
}
// #[test]
// fn eq_trig_33() {
//     check(
//         "(- (/ 1 (- (sec t) (tan t))) (/ 1 (cos t)))",
//         "(- (/ 1 (cos t)) (/ 1 (+ (sec t) (tan t))))",
//     )
// }
#[test]
fn eq_trig_34() {
    check(
        "(+ (/ (tan t) (+ (sec t) 1)) (/ (tan t) (- (sec t) 1)))",
        "(* 2 (csc t))",
    )
}
#[test]
fn eq_trig_35() {
    check(
        "(* (- (+ (sec t) (tan t)) 1) (+ (- (sec t) (tan t)) 1))",
        "(* 2 (tan t))",
    )
}
#[test]
fn eq_trig_36() {
    check(
        "(/ (+ (tan A) (cot B)) (+ (cot A) (tan B)))",
        "(/ (tan A) (tan B))",
    )
}
#[test]
fn eq_trig_37() {
    // This is pretty tricky and needs to rewrite 1 => (sec x)^2 - (tan x)^2 in the numerator only
    check(
        "(/ (- (+ (tan A) (sec A)) 1) (+ (- (tan A) (sec A)) 1))",
        "(/ (+ 1 (sin A)) (cos A))",
    )
}
#[test]
fn eq_trig_38() {
    check(
        "(- (/ (+ 1 (sin a)) (- (csc a) (cot a))) (/ (- 1 (sin a)) (+ (csc a) (cot a))))",
        "(* 2 (+ 1 (cot a)))",
    )
}
#[test]
fn eq_trig_39() {
    check(
        "(+ (/ 1 (- (+ (cos t) (sin t)) 1)) (/ 1 (+ (+ (cos t) (sin t)) 1)))",
        "(+ (sec t) (csc t))",
    )
}
#[test]
fn eq_trig_40() {
    check(
        "(+ (/ (tan A) (- 1 (cot A))) (/ (cot A) (- 1 (tan A))))",
        "(+ 1 (* (sec A) (csc A)))",
    )
}
#[test]
fn eq_trig_41() {
    check(
        "(- (pow (- (sec x) 1) 2) (pow (- (tan x) (sin x)) 2))",
        "(pow (- 1 (cos x)) 2)",
    )
}

// ─── Stochastic search ────────────────────────────────────────────────────────

/// Stochastic analysis for `Trig`: constant-folds integer arithmetic,
/// stores `None` for any node that is not a statically-known integer.
#[derive(Default)]
struct TrigStoAnalysis;

impl StoAnalysis<Trig> for TrigStoAnalysis {
    type Data = Option<i32>;

    fn make(&self, enode: &Trig, analysis: &[Option<i32>]) -> Option<i32> {
        let x = |i: &Id| analysis[usize::from(*i)];
        match enode {
            Trig::Num(n) => Some(*n),
            Trig::Add([a, b]) => x(a)?.checked_add(x(b)?),
            Trig::Sub([a, b]) => x(a)?.checked_sub(x(b)?),
            Trig::Mul([a, b]) => x(a)?.checked_mul(x(b)?),
            Trig::Pow([a, b]) => {
                let base = x(a)?;
                let exp = x(b)?;
                if exp < 0 {
                    return None;
                }
                base.checked_pow(exp as u32)
            }
            _ => None,
        }
    }
}

type TrigState = State<Trig, TrigStoAnalysis>;
type TrigRw = StoRewrite<Trig, TrigStoAnalysis>;

/// Constant-fold a newly created node; return a replacement `Trig::Num` when
/// both children (if any) are known integers.
fn normalize_trig(state: &mut TrigState, _id: Id, node: Trig) -> Option<Trig> {
    let val = |id: Id| -> Option<i32> { state.analysis[usize::from(id)] };
    match node {
        Trig::Add([a, b]) => Some(Trig::Num(val(a)?.checked_add(val(b)?)?)),
        Trig::Sub([a, b]) => Some(Trig::Num(val(a)?.checked_sub(val(b)?)?)),
        Trig::Mul([a, b]) => Some(Trig::Num(val(a)?.checked_mul(val(b)?)?)),
        Trig::Pow([a, b]) => {
            let base = val(a)?;
            let exp = val(b)?;
            if exp < 0 {
                return None;
            }
            Some(Trig::Num(base.checked_pow(exp as u32)?))
        }
        _ => None,
    }
}

fn p_trig(s: &str) -> Pattern<Trig> {
    s.parse().unwrap()
}

fn sto_rw(name: &str, lhs: &str, rhs: &str) -> TrigRw {
    StoRewrite::new(name, p_trig(lhs), p_trig(rhs)).unwrap()
}

#[rustfmt::skip]
fn sto_rules(vars: impl Iterator<Item = Symbol>) -> Vec<TrigRw> {
    let mut rwts: Vec<TrigRw> = vec![
    // trig definitions
    sto_rw("expand-tan",   "(tan ?x)",              "(/ (sin ?x) (cos ?x))"),
    sto_rw("i-expand-tan", "(/ (sin ?x) (cos ?x))", "(tan ?x)"),
    sto_rw("expand-cot",   "(cot ?x)",              "(/ (cos ?x) (sin ?x))"),
    sto_rw("i-expand-cot", "(/ (cos ?x) (sin ?x))", "(cot ?x)"),
    sto_rw("expand-sec",   "(sec ?x)",              "(/ 1 (cos ?x))"),
    sto_rw("i-expand-sec", "(/ 1 (cos ?x))",        "(sec ?x)"),
    sto_rw("expand-csc",   "(csc ?x)",              "(/ 1 (sin ?x))"),
    sto_rw("i-expand-csc", "(/ 1 (sin ?x))",        "(csc ?x)"),

    // trig identities
    sto_rw("pythag",     "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))", "1"),
    sto_rw("pythag-sin", "(pow (sin ?x) 2)", "(- 1 (pow (cos ?x) 2))"),
    sto_rw("i-pythag-sin", "(- 1 (pow (cos ?x) 2))", "(pow (sin ?x) 2)"),
    sto_rw("pythag-cos", "(pow (cos ?x) 2)", "(- 1 (pow (sin ?x) 2))"),
    sto_rw("i-pythag-cos", "(- 1 (pow (sin ?x) 2))", "(pow (cos ?x) 2)"),
    sto_rw("pythag-sec",   "(+ 1 (pow (tan ?x) 2))", "(pow (sec ?x) 2)"),
    sto_rw("i-pythag-sec", "(pow (sec ?x) 2)",        "(+ 1 (pow (tan ?x) 2))"),
    sto_rw("pythag-csc",   "(+ 1 (pow (cot ?x) 2))", "(pow (csc ?x) 2)"),
    sto_rw("i-pythag-csc", "(pow (csc ?x) 2)",        "(+ 1 (pow (cot ?x) 2))"),

    // commutativity and associativity
    sto_rw("comm-add",   "(+ ?a ?b)",          "(+ ?b ?a)"),
    sto_rw("comm-mul",   "(* ?a ?b)",          "(* ?b ?a)"),
    sto_rw("assoc-add",  "(+ (+ ?a ?b) ?c)",   "(+ ?a (+ ?b ?c))"),
    sto_rw("i-assoc-add","(+ ?a (+ ?b ?c))",   "(+ (+ ?a ?b) ?c)"),
    sto_rw("assoc-mul",  "(* (* ?a ?b) ?c)",   "(* ?a (* ?b ?c))"),
    sto_rw("i-assoc-mul","(* ?a (* ?b ?c))",   "(* (* ?a ?b) ?c)"),

    // distributivity
    sto_rw("distribute", "(* ?a (+ ?b ?c))",          "(+ (* ?a ?b) (* ?a ?c))"),
    sto_rw("factor",     "(+ (* ?a ?b) (* ?a ?c))",   "(* ?a (+ ?b ?c))"),
    sto_rw("factor-sub", "(- (* ?a ?b) (* ?a ?c))",   "(* ?a (- ?b ?c))"),

    // algebraic
    sto_rw("zero-add",   "(+ ?a 0)",           "?a"),
    sto_rw("add-zero",   "?a",                 "(+ ?a 0)"),
    sto_rw("one-mul",    "(* ?a 1)",           "?a"),
    sto_rw("mul-one",    "?a",                 "(* ?a 1)"),
    sto_rw("zero-mul",   "(* ?a 0)",           "0"),
    sto_rw("cancel-add", "(+ ?a (* -1 ?a))",   "0"),
    sto_rw("recip-mul",  "(* ?a (/ 1 ?a))",    "1"),
    sto_rw("double-neg", "(* -1 (* -1 ?a))",   "?a"),

    // subtraction and division as sugar
    sto_rw("sub-canon",   "(- ?a ?b)",           "(+ ?a (* -1 ?b))"),
    sto_rw("i-sub-canon", "(+ ?a (* -1 ?b))",    "(- ?a ?b)"),
    sto_rw("div-canon",   "(/ ?a ?b)",           "(* ?a (/ 1 ?b))"),
    sto_rw("i-div-canon", "(* ?a (/ 1 ?b))",     "(/ ?a ?b)"),

    // fractions
    sto_rw("frac-add",           "(+ (/ ?a ?b) (/ ?c ?d))", "(/ (+ (* ?a ?d) (* ?b ?c)) (* ?b ?d))"),
    sto_rw("i-frac-add",         "(/ (+ (* ?a ?d) (* ?b ?c)) (* ?b ?d))", "(+ (/ ?a ?b) (/ ?c ?d))"),
    sto_rw("frac-add-same-denom","(+ (/ ?a ?b) (/ ?c ?b))", "(/ (+ ?a ?c) ?b)"),
    sto_rw("i-frac-add-same-denom", "(/ (+ ?a ?c) ?b)", "(+ (/ ?a ?b) (/ ?c ?b))"),
    sto_rw("frac-mul",           "(* (/ ?a ?b) (/ ?c ?d))", "(/ (* ?a ?c) (* ?b ?d))"),
    sto_rw("i-frac-mul",         "(/ (* ?a ?c) (* ?b ?d))", "(* (/ ?a ?b) (/ ?c ?d))"),
    sto_rw("recip-frac",         "(/ 1 (/ ?a ?b))",         "(/ ?b ?a)"),
    sto_rw("i-recip-frac",       "(/ ?b ?a)",               "(/ 1 (/ ?a ?b))"),
    sto_rw("cancel-frac",        "(/ (* ?a ?c) (* ?b ?c))", "(/ ?a ?b)"),
    sto_rw("split-frac",         "(/ (+ ?a ?c) ?c)",        "(+ (/ ?a ?c) 1)"),
    sto_rw("i-split-frac",       "(+ (/ ?a ?c) 1)",         "(/ (+ ?a ?c) ?c)"),

    // powers
    sto_rw("pow2",     "(pow ?a 2)",             "(* ?a ?a)"),
    sto_rw("i-pow2",   "(* ?a ?a)",              "(pow ?a 2)"),
    sto_rw("pow3",     "(pow ?a 3)",             "(* ?a (pow ?a 2))"),
    sto_rw("i-pow3",   "(* ?a (pow ?a 2))",      "(pow ?a 3)"),
    sto_rw("pow4",     "(pow ?a 4)",             "(pow (pow ?a 2) 2)"),
    sto_rw("i-pow4",   "(pow (pow ?a 2) 2)",     "(pow ?a 4)"),
    sto_rw("pow-mul",  "(pow (* ?a ?b) ?n)",     "(* (pow ?a ?n) (pow ?b ?n))"),
    sto_rw("i-pow-mul","(* (pow ?a ?n) (pow ?b ?n))", "(pow (* ?a ?b) ?n)"),
    sto_rw("pow-div",  "(pow (/ ?a ?b) ?n)",     "(/ (pow ?a ?n) (pow ?b ?n))"),
    sto_rw("i-pow-div","(/ (pow ?a ?n) (pow ?b ?n))", "(pow (/ ?a ?b) ?n)"),

    // factoring
    sto_rw("diff-sq",   "(- (pow ?a 2) (pow ?b 2))", "(* (+ ?a ?b) (- ?a ?b))"),
    sto_rw("i-diff-sq", "(* (+ ?a ?b) (- ?a ?b))",   "(- (pow ?a 2) (pow ?b 2))"),
    sto_rw("sum-cubes",
        "(+ (pow ?a 3) (pow ?b 3))",
        "(* (+ ?a ?b) (+ (- (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    sto_rw("i-sum-cubes",
        "(* (+ ?a ?b) (+ (- (pow ?a 2) (* ?a ?b)) (pow ?b 2)))",
        "(+ (pow ?a 3) (pow ?b 3))"),
    sto_rw("diff-cubes",
        "(- (pow ?a 3) (pow ?b 3))",
        "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    sto_rw("i-diff-cubes",
        "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))",
        "(- (pow ?a 3) (pow ?b 3))"),
    ];
    for var in vars {
        let name = format!("i-pythag-{}", var);
        let rhs = format!("(+ (pow (sin {}) 2) (pow (cos {}) 2))", var, var);
        rwts.push(sto_rw(&name, "1", &rhs));
    }
    rwts
}

fn sto_simplify(s: &str) -> (f64, RecExpr<Trig>) {
    let n_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let timeout = Duration::from_secs(10);
    let initial_expr: Arc<RecExpr<Trig>> = Arc::new(s.parse().unwrap());
    let vars: HashSet<Symbol> = initial_expr
        .as_ref()
        .iter()
        .filter_map(|n| {
            if let Trig::Symbol(s) = n {
                Some(*s)
            } else {
                None
            }
        })
        .collect();

    let handles: Vec<_> = (0..n_threads)
        .map(|i| {
            let initial_expr = Arc::clone(&initial_expr);
            let vars = vars.clone();
            let seed = 42u64 + i as u64;
            std::thread::spawn(move || {
                let mut runner =
                    StoRunner::new((*initial_expr).clone(), sto_rules(vars.into_iter()))
                        .with_normalizer(normalize_trig);
                let mut rng = SimpleLcg::new(seed);
                let config = StoConfig {
                    max_stall: 10_000,
                    max_restart: usize::MAX,
                    max_iter: usize::MAX,
                    max_time: timeout,
                    beta_schedule: Box::new(PeriodicBeta {
                        random_walk_steps: 20,
                        beta: 1.0,
                        interval: 100,
                    }),
                };
                runner.run(config, &mut rng);
                (runner.best_cost, runner.best_expr.clone())
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    results
        .into_iter()
        .min_by(|a, b| a.0.partial_cmp(&b.0).unwrap())
        .unwrap()
}

/// Run stochastic search and return `(cost, best_expr_string, is_optimal)`.
fn run_eqsat_test(lhs: &str, rhs: &str, explain: bool) -> (usize, String, bool) {
    let (cost, best) = simplify(lhs, explain);
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr);
    let is_optimal = cost <= expected_cost;
    (cost, best, is_optimal)
}

fn run_sto_test(lhs: &str, rhs: &str) -> (f64, String, bool) {
    let (cost, best) = sto_simplify(lhs);
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr) as f64;
    let is_optimal = cost <= expected_cost;
    (cost, best.to_string(), is_optimal)
}

fn sto_check(lhs: &str, rhs: &str) {
    let (cost, best, is_optimal) = run_sto_test(lhs, rhs);
    eprintln!("best cost: {}, best expr: {}", cost, best);
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr) as f64;
    assert!(
        is_optimal,
        "expected cost <= {}, got cost {} with: {}",
        expected_cost, cost, best
    );
}

#[test]
#[serial]
fn sto_trig_01() {
    sto_check("(* (* (sin t) (cos t)) (+ (tan t) (cot t)))", "1")
}
#[test]
#[serial]
fn sto_trig_02() {
    sto_check(
        "(- (pow (sin t) 4) (pow (cos t) 4))",
        "(- (* 2 (pow (sin t) 2)) 1)",
    )
}
#[test]
#[serial]
fn sto_trig_03() {
    sto_check(
        "(+ (- (pow (sin t) 4) (pow (cos t) 4)) 1)",
        "(* 2 (pow (sin t) 2))",
    )
}
#[test]
#[serial]
fn sto_trig_04() {
    sto_check(
        "(- (pow (cos t) 4) (pow (sin t) 4))",
        "(- (* 2 (pow (cos t) 2)) 1)",
    )
}
#[test]
#[serial]
fn sto_trig_05() {
    sto_check(
        "(* (* (sin a) (cos a)) (- (tan a) (cot a)))",
        "(- (* 2 (pow (sin a) 2)) 1)",
    )
}
#[test]
#[serial]
fn sto_trig_06() {
    sto_check(
        "(+ (pow (+ (cos A) (sin A)) 2) (pow (- (cos A) (sin A)) 2))",
        "2",
    )
}
#[test]
#[serial]
fn sto_trig_07() {
    sto_check(
        "(+ (pow (+ 1 (tan t)) 2) (pow (- 1 (tan t)) 2))",
        "(* 2 (pow (sec t) 2))",
    )
}
#[test]
#[serial]
fn sto_trig_08() {
    sto_check(
        "(+ (/ 1 (+ 1 (cos A))) (/ 1 (- 1 (cos A))))",
        "(* 2 (pow (csc A) 2))",
    )
}
#[test]
#[serial]
fn sto_trig_09() {
    sto_check(
        "(/ (+ 1 (cos t)) (- 1 (cos t)))",
        "(pow (+ (cot t) (csc t)) 2)",
    )
}
#[test]
#[serial]
fn sto_trig_10() {
    sto_check(
        "(- (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
        "(* 2 (* (tan A) (sec A)))",
    )
}
#[test]
#[serial]
fn sto_trig_11() {
    sto_check(
        "(+ (/ 1 (- 1 (cos A))) (/ 1 (+ 1 (cos A))))",
        "(* 2 (* (cot A) (csc A)))",
    )
}
#[test]
#[serial]
fn sto_trig_12() {
    sto_check(
        "(* (+ (+ 1 (sec A)) (tan A)) (+ (- 1 (csc A)) (cot A)))",
        "2",
    )
}
#[test]
#[serial]
fn sto_trig_13() {
    sto_check(
        "(+ (/ (cos A) (+ 1 (sin A))) (/ (cos A) (- 1 (sin A))))",
        "(* 2 (sec A))",
    )
}
#[test]
#[serial]
fn sto_trig_14() {
    sto_check(
        "(+ (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
        "(* 2 (pow (sec A) 2))",
    )
}
#[test]
#[serial]
fn sto_trig_15() {
    sto_check(
        "(+ (/ 1 (+ (sin A) (cos A))) (/ 1 (- (sin A) (cos A))))",
        "(/ (* 2 (sin A)) (- 1 (pow (cos A) 2)))",
    )
}
#[test]
#[serial]
fn sto_trig_16() {
    sto_check(
        "(/ (+ 1 (sin t)) (- 1 (sin t)))",
        "(pow (+ (sec t) (tan t)) 2)",
    )
}
// #[test]
// #[serial]
// fn sto_trig_17() {
//     sto_check("(/ (- 1 (sin A)) (cos A))", "(/ (cos A) (+ 1 (sin A)))")
// }
#[test]
#[serial]
fn sto_trig_18() {
    sto_check(
        "(+ (/ (cos t) (+ 1 (sin t))) (/ (+ 1 (sin t)) (cos t)))",
        "(* 2 (sec t))",
    )
}
// #[test]
// #[serial]
// fn sto_trig_19() {
//     sto_check(
//         "(pow (/ (+ 1 (cos A)) (sin A)) 2)",
//         "(/ (+ 1 (cos A)) (- 1 (cos A)))",
//     )
// }
#[test]
#[serial]
fn sto_trig_20() {
    sto_check(
        "(+ (/ (sin A) (+ 1 (cos A))) (/ (+ 1 (cos A)) (sin A)))",
        "(* 2 (csc A))",
    )
}
#[test]
#[serial]
fn sto_trig_21() {
    sto_check(
        "(* (* (+ 1 (cos t)) (- 1 (cos t))) (+ 1 (pow (cot t) 2)))",
        "1",
    )
}
#[test]
#[serial]
fn sto_trig_22() {
    sto_check("(* (* (+ 1 (pow (tan A) 2)) (sin A)) (cos A))", "(tan A)")
}
#[test]
#[serial]
fn sto_trig_23() {
    sto_check(
        "(/ (- (pow (sin b) 2) (pow (sin a) 2)) (* (pow (sin a) 2) (pow (sin b) 2)))",
        "(+ (pow (cot a) 2) (pow (cot b) 2))",
    )
}
// #[test]
// #[serial]
// fn sto_trig_24() {
//     sto_check("(+ (tan A) (cot A))", "(* (sec A) (csc A))")
// }
#[test]
#[serial]
fn sto_trig_25() {
    sto_check("(/ (csc A) (+ (tan A) (cot A)))", "(cos A)")
}
// #[test]
// #[serial]
// fn sto_trig_26() {
//     sto_check(
//         "(+ (pow (sec t) 2) (pow (csc t) 2))",
//         "(* (pow (sec t) 2) (pow (csc t) 2))",
//     )
// }
#[test]
#[serial]
fn sto_trig_27() {
    sto_check(
        "(+ (+ (pow (tan t) 2) (pow (cot t) 2)) 2)",
        "(* (pow (sec t) 2) (pow (csc t) 2))",
    )
}
// #[test]
// #[serial]
// fn sto_trig_28() {
//     sto_check(
//         "(+ (pow (tan t) 4) (pow (tan t) 2))",
//         "(- (pow (sec t) 4) (pow (sec t) 2))",
//     )
// }
#[test]
#[serial]
fn sto_trig_29() {
    sto_check(
        "(+ (- (pow (csc t) 4) (* 2 (pow (csc t) 2))) (- (* 2 (pow (sec t) 2)) (pow (sec t) 4)))",
        "(- (pow (cot t) 4) (pow (tan t) 4))",
    )
}
#[test]
#[serial]
fn sto_trig_30() {
    sto_check(
        "(/ (- (sin A) (* 2 (pow (sin A) 3))) (- (* 2 (pow (cos A) 3)) (cos A)))",
        "(tan A)",
    )
}
#[test]
#[serial]
fn sto_trig_31() {
    sto_check(
        "(+ (/ (cos t) (+ (csc t) 1)) (/ (cos t) (- (csc t) 1)))",
        "(* 2 (tan t))",
    )
}
#[test]
#[serial]
fn sto_trig_32() {
    sto_check(
        "(+ (/ (cos t) (- 1 (tan t))) (/ (sin t) (- 1 (cot t))))",
        "(+ (sin t) (cos t))",
    )
}
// #[test]
// #[serial]
// fn sto_trig_33() {
//     sto_check(
//         "(- (/ 1 (- (sec t) (tan t))) (/ 1 (cos t)))",
//         "(- (/ 1 (cos t)) (/ 1 (+ (sec t) (tan t))))",
//     )
// }
#[test]
#[serial]
fn sto_trig_34() {
    sto_check(
        "(+ (/ (tan t) (+ (sec t) 1)) (/ (tan t) (- (sec t) 1)))",
        "(* 2 (csc t))",
    )
}
#[test]
#[serial]
fn sto_trig_35() {
    sto_check(
        "(* (- (+ (sec t) (tan t)) 1) (+ (- (sec t) (tan t)) 1))",
        "(* 2 (tan t))",
    )
}
#[test]
#[serial]
fn sto_trig_36() {
    sto_check(
        "(/ (+ (tan A) (cot B)) (+ (cot A) (tan B)))",
        "(/ (tan A) (tan B))",
    )
}
#[test]
#[serial]
fn sto_trig_37() {
    sto_check(
        "(/ (- (+ (tan A) (sec A)) 1) (+ (- (tan A) (sec A)) 1))",
        "(/ (+ 1 (sin A)) (cos A))",
    )
}
#[test]
#[serial]
fn sto_trig_38() {
    sto_check(
        "(- (/ (+ 1 (sin a)) (- (csc a) (cot a))) (/ (- 1 (sin a)) (+ (csc a) (cot a))))",
        "(* 2 (+ 1 (cot a)))",
    )
}
#[test]
#[serial]
fn sto_trig_39() {
    sto_check(
        "(+ (/ 1 (- (+ (cos t) (sin t)) 1)) (/ 1 (+ (+ (cos t) (sin t)) 1)))",
        "(+ (sec t) (csc t))",
    )
}
#[test]
#[serial]
fn sto_trig_40() {
    sto_check(
        "(+ (/ (tan A) (- 1 (cot A))) (/ (cot A) (- 1 (tan A))))",
        "(+ 1 (* (sec A) (csc A)))",
    )
}
#[test]
#[serial]
fn sto_trig_41() {
    sto_check(
        "(- (pow (- (sec x) 1) 2) (pow (- (tan x) (sin x)) 2))",
        "(pow (- 1 (cos x)) 2)",
    )
}

// ─── Main ─────────────────────────────────────────────────────────────────────

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let explain = args.iter().any(|a| a == "--explain");
    let filters: Vec<&str> = args
        .iter()
        .filter(|a| *a != "--explain")
        .map(|s| s.as_str())
        .collect();

    let tests: &[(&str, &str, &str)] = &[
        (
            "trig_01",
            "(* (* (sin t) (cos t)) (+ (tan t) (cot t)))",
            "1",
        ),
        (
            "trig_02",
            "(- (pow (sin t) 4) (pow (cos t) 4))",
            "(- (* 2 (pow (sin t) 2)) 1)",
        ),
        (
            "trig_03",
            "(+ (- (pow (sin t) 4) (pow (cos t) 4)) 1)",
            "(* 2 (pow (sin t) 2))",
        ),
        (
            "trig_04",
            "(- (pow (cos t) 4) (pow (sin t) 4))",
            "(- (* 2 (pow (cos t) 2)) 1)",
        ),
        (
            "trig_05",
            "(* (* (sin a) (cos a)) (- (tan a) (cot a)))",
            "(- (* 2 (pow (sin a) 2)) 1)",
        ),
        (
            "trig_06",
            "(+ (pow (+ (cos A) (sin A)) 2) (pow (- (cos A) (sin A)) 2))",
            "2",
        ),
        (
            "trig_07",
            "(+ (pow (+ 1 (tan t)) 2) (pow (- 1 (tan t)) 2))",
            "(* 2 (pow (sec t) 2))",
        ),
        (
            "trig_08",
            "(+ (/ 1 (+ 1 (cos A))) (/ 1 (- 1 (cos A))))",
            "(* 2 (pow (csc A) 2))",
        ),
        (
            "trig_09",
            "(/ (+ 1 (cos t)) (- 1 (cos t)))",
            "(pow (+ (cot t) (csc t)) 2)",
        ),
        (
            "trig_10",
            "(- (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
            "(* 2 (* (tan A) (sec A)))",
        ),
        (
            "trig_11",
            "(+ (/ 1 (- 1 (cos A))) (/ 1 (+ 1 (cos A))))",
            "(* 2 (* (cot A) (csc A)))",
        ),
        (
            "trig_12",
            "(* (+ (+ 1 (sec A)) (tan A)) (+ (- 1 (csc A)) (cot A)))",
            "2",
        ),
        (
            "trig_13",
            "(+ (/ (cos A) (+ 1 (sin A))) (/ (cos A) (- 1 (sin A))))",
            "(* 2 (sec A))",
        ),
        (
            "trig_14",
            "(+ (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))",
            "(* 2 (pow (sec A) 2))",
        ),
        (
            "trig_15",
            "(+ (/ 1 (+ (sin A) (cos A))) (/ 1 (- (sin A) (cos A))))",
            "(/ (* 2 (sin A)) (- 1 (pow (cos A) 2)))",
        ),
        (
            "trig_16",
            "(/ (+ 1 (sin t)) (- 1 (sin t)))",
            "(pow (+ (sec t) (tan t)) 2)",
        ),
        // (
        //     "trig_17",
        //     "(/ (- 1 (sin A)) (cos A))",
        //     "(/ (cos A) (+ 1 (sin A)))",
        // ),
        (
            "trig_18",
            "(+ (/ (cos t) (+ 1 (sin t))) (/ (+ 1 (sin t)) (cos t)))",
            "(* 2 (sec t))",
        ),
        // (
        //     "trig_19",
        //     "(pow (/ (+ 1 (cos A)) (sin A)) 2)",
        //     "(/ (+ 1 (cos A)) (- 1 (cos A)))",
        // ),
        (
            "trig_20",
            "(+ (/ (sin A) (+ 1 (cos A))) (/ (+ 1 (cos A)) (sin A)))",
            "(* 2 (csc A))",
        ),
        (
            "trig_21",
            "(* (* (+ 1 (cos t)) (- 1 (cos t))) (+ 1 (pow (cot t) 2)))",
            "1",
        ),
        (
            "trig_22",
            "(* (* (+ 1 (pow (tan A) 2)) (sin A)) (cos A))",
            "(tan A)",
        ),
        (
            "trig_23",
            "(/ (- (pow (sin b) 2) (pow (sin a) 2)) (* (pow (sin a) 2) (pow (sin b) 2)))",
            "(+ (pow (cot a) 2) (pow (cot b) 2))",
        ),
        // ("trig_24", "(+ (tan A) (cot A))", "(* (sec A) (csc A))"),
        ("trig_25", "(/ (csc A) (+ (tan A) (cot A)))", "(cos A)"),
        // (
        //     "trig_26",
        //     "(+ (pow (sec t) 2) (pow (csc t) 2))",
        //     "(* (pow (sec t) 2) (pow (csc t) 2))",
        // ),
        (
            "trig_27",
            "(+ (+ (pow (tan t) 2) (pow (cot t) 2)) 2)",
            "(* (pow (sec t) 2) (pow (csc t) 2))",
        ),
        // (
        //     "trig_28",
        //     "(+ (pow (tan t) 4) (pow (tan t) 2))",
        //     "(- (pow (sec t) 4) (pow (sec t) 2))",
        // ),
        (
            "trig_29",
            "(+ (- (pow (csc t) 4) (* 2 (pow (csc t) 2))) (- (* 2 (pow (sec t) 2)) (pow (sec t) 4)))",
            "(- (pow (cot t) 4) (pow (tan t) 4))",
        ),
        (
            "trig_30",
            "(/ (- (sin A) (* 2 (pow (sin A) 3))) (- (* 2 (pow (cos A) 3)) (cos A)))",
            "(tan A)",
        ),
        (
            "trig_31",
            "(+ (/ (cos t) (+ (csc t) 1)) (/ (cos t) (- (csc t) 1)))",
            "(* 2 (tan t))",
        ),
        (
            "trig_32",
            "(+ (/ (cos t) (- 1 (tan t))) (/ (sin t) (- 1 (cot t))))",
            "(+ (sin t) (cos t))",
        ),
        // (
        //     "trig_33",
        //     "(- (/ 1 (- (sec t) (tan t))) (/ 1 (cos t)))",
        //     "(- (/ 1 (cos t)) (/ 1 (+ (sec t) (tan t))))",
        // ),
        (
            "trig_34",
            "(+ (/ (tan t) (+ (sec t) 1)) (/ (tan t) (- (sec t) 1)))",
            "(* 2 (csc t))",
        ),
        (
            "trig_35",
            "(* (- (+ (sec t) (tan t)) 1) (+ (- (sec t) (tan t)) 1))",
            "(* 2 (tan t))",
        ),
        (
            "trig_36",
            "(/ (+ (tan A) (cot B)) (+ (cot A) (tan B)))",
            "(/ (tan A) (tan B))",
        ),
        (
            "trig_37",
            "(/ (- (+ (tan A) (sec A)) 1) (+ (- (tan A) (sec A)) 1))",
            "(/ (+ 1 (sin A)) (cos A))",
        ),
        (
            "trig_38",
            "(- (/ (+ 1 (sin a)) (- (csc a) (cot a))) (/ (- 1 (sin a)) (+ (csc a) (cot a))))",
            "(* 2 (+ 1 (cot a)))",
        ),
        (
            "trig_39",
            "(+ (/ 1 (- (+ (cos t) (sin t)) 1)) (/ 1 (+ (+ (cos t) (sin t)) 1)))",
            "(+ (sec t) (csc t))",
        ),
        (
            "trig_40",
            "(+ (/ (tan A) (- 1 (cot A))) (/ (cot A) (- 1 (tan A))))",
            "(+ 1 (* (sec A) (csc A)))",
        ),
        (
            "trig_41",
            "(- (pow (- (sec x) 1) 2) (pow (- (tan x) (sin x)) 2))",
            "(pow (- 1 (cos x)) 2)",
        ),
    ];

    let mut eqsat_passed = 0usize;
    let mut sto_passed = 0usize;
    let mut rows: Vec<String> =
        vec!["name,eqsat_cost,eqsat_expr,eqsat_optimal,sto_cost,sto_expr,sto_optimal".to_string()];

    let active_tests: Vec<_> = tests
        .iter()
        .filter(|(name, _, _)| filters.is_empty() || filters.contains(name))
        .collect();

    for (name, lhs, rhs) in &active_tests {
        print!("{name} eqsat ... ");
        let (eq_cost, eq_expr, eq_optimal) = run_eqsat_test(lhs, rhs, explain);
        if eq_optimal {
            eqsat_passed += 1;
            println!("ok (cost {eq_cost})");
        } else {
            println!("FAIL (cost {eq_cost}, got: {eq_expr})");
        }

        print!("{name} sto   ... ");
        let (sto_cost, sto_expr, sto_optimal) = run_sto_test(lhs, rhs);
        if sto_optimal {
            sto_passed += 1;
            println!("ok (cost {sto_cost})");
        } else {
            println!("FAIL (cost {sto_cost}, got: {sto_expr})");
        }

        let eq_escaped = eq_expr.replace('"', "\"\"");
        let sto_escaped = sto_expr.replace('"', "\"\"");
        rows.push(format!(
            "{name},{eq_cost},\"{eq_escaped}\",{eq_optimal},{sto_cost},\"{sto_escaped}\",{sto_optimal}"
        ));
    }

    println!("\neqsat: {eqsat_passed}/{} passed", active_tests.len());
    println!("sto:   {sto_passed}/{} passed", active_tests.len());

    let csv = rows.join("\n");
    std::fs::write("trig_results.csv", csv).expect("failed to write trig_results.csv");
    println!("Results saved to trig_results.csv");
}
