use clap::Parser;
use core::f64;
use egg::stochastic::{
    IterHookAction, PeriodicBeta, SimpleLcg, State, StoAnalysis, StoConditionalApplier, StoConfig,
    StoRewrite, StoRunner, StoSearcher,
};
use egg::{rewrite as rw, *};
use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

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

struct IsNotZero {
    var: Var,
}

impl Condition<Trig, ConstantFold> for IsNotZero {
    fn check(&self, egraph: &mut EGraph, _eclass: Id, subst: &Subst) -> bool {
        !matches!(&egraph[subst[self.var]].data, Some((0, _)))
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
    rw!("recip-mul";     "(* ?a (/ 1 ?a))" => "1" if IsNotZero { var: "?a".parse().unwrap() }),
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
    rw!("i-recip-frac";  "(/ ?b ?a)" => "(/ 1 (/ ?a ?b))" if IsNotZero { var: "?b".parse().unwrap() }),
    rw!("cancel-frac";   "(/ (* ?a ?c) (* ?b ?c))" => "(/ ?a ?b)" if IsNotZero { var: "?c".parse().unwrap() }),
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
    // for var in vars {
    //     let name = format!("i-pythag-{}", var);
    //     let rhs = format!("(+ (pow (sin {}) 2) (pow (cos {}) 2))", var, var);
    //     rwts.push(Rewrite::new(name, "1".parse::<Pattern<Trig>>().unwrap(), rhs.parse::<Pattern<Trig>>().unwrap()).unwrap());
    // }
    rwts
}

fn simplify(s: &str) -> (usize, String) {
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
    let runner = Runner::default()
        .with_expr(&expr)
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
    println!("{}", runner.report());
    (best_cost, best.to_string())
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

fn sto_rw_if(
    name: &str,
    lhs: &str,
    rhs: &str,
    cond: impl Fn(&TrigState, Id, &Subst) -> bool + Send + Sync + 'static,
) -> TrigRw {
    StoRewrite::new(
        name,
        p_trig(lhs),
        StoConditionalApplier {
            applier: Arc::new(p_trig(rhs)),
            condition: Box::new(cond),
        },
    )
    .unwrap()
}

fn sto_is_not_zero(var: &str) -> impl Fn(&TrigState, Id, &Subst) -> bool + Send + Sync + 'static {
    let v: Var = var.parse().unwrap();
    move |s: &TrigState, _: Id, subst: &Subst| match s.rec_expr[subst[v]] {
        Trig::Num(n) => n != 0,
        _ => true,
    }
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
    sto_rw_if("i-recip-frac",       "(/ ?b ?a)",               "(/ 1 (/ ?a ?b))", sto_is_not_zero("?b")),
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
    // for var in vars {
    //     let name = format!("i-pythag-{}", var);
    //     let rhs = format!("(+ (pow (sin {}) 2) (pow (cos {}) 2))", var, var);
    //     rwts.push(sto_rw(&name, "1", &rhs));
    // }
    rwts
}

/// Returns `(best_cost, best_expr, total_proposals, total_accepted)`.
/// The proposal/accepted counts are the sum across all threads.
fn sto_simplify(
    s: &str,
    n_threads: usize,
    max_time: Duration,
    target_cost: Option<f64>,
) -> (f64, RecExpr<Trig>, u64, u64) {
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

    let should_abort = Arc::new(AtomicBool::new(false));
    let handles: Vec<_> = (0..n_threads)
        .map(|i| {
            let initial_expr = Arc::clone(&initial_expr);
            let should_abort = should_abort.clone();
            let vars = vars.clone();
            let seed = 0u64 + i as u64;
            std::thread::spawn(move || {
                let mut runner =
                    StoRunner::new((*initial_expr).clone(), sto_rules(vars.into_iter()))
                        .with_normalizer(normalize_trig);
                let bad_pattern = "(/ ?x 0)".parse::<Pattern<Trig>>().unwrap();
                let mut best_cost = f64::INFINITY;
                if let Some(target) = target_cost {
                    runner = runner.with_iter_hook(move |r| {
                        if r.best_cost < best_cost {
                            best_cost = r.best_cost;
                            if bad_pattern.search_pos(&r.state, r.current_root).is_some() {
                                return IterHookAction::Restart;
                            }
                        }
                        if r.best_cost <= target {
                            should_abort.store(true, Ordering::Relaxed);
                            IterHookAction::Abort
                        } else if should_abort.load(Ordering::Relaxed) {
                            IterHookAction::Abort
                        } else {
                            IterHookAction::Continue
                        }
                    });
                }
                let mut rng = SimpleLcg::new(seed);
                let config = StoConfig {
                    max_stall: 10_000,
                    max_restart: usize::MAX,
                    max_iter: usize::MAX,
                    max_time,
                    beta_schedule: Box::new(PeriodicBeta {
                        random_walk_steps: 20,
                        beta: 1.0,
                        interval: 100,
                    }),
                };
                runner.run(config, &mut rng);
                (
                    runner.best_cost,
                    runner.best_expr.clone(),
                    runner.n_proposed,
                    runner.n_accepted,
                )
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    let total_proposed: u64 = results.iter().map(|r| r.2).sum();
    let total_accepted: u64 = results.iter().map(|r| r.3).sum();
    let (best_cost, best_expr, _, _) = results
        .into_iter()
        .min_by(|a, b| a.0.partial_cmp(&b.0).unwrap())
        .unwrap();
    (best_cost, best_expr, total_proposed, total_accepted)
}

/// Run stochastic search and return `(cost, best_expr_string, is_optimal)`.
fn run_eqsat_test(lhs: &str, rhs: &str) -> (usize, String, bool) {
    let (cost, best) = simplify(lhs);
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr);
    let is_optimal = cost <= expected_cost;
    (cost, best, is_optimal)
}

fn run_sto_test(
    lhs: &str,
    rhs: &str,
    n_threads: usize,
    max_time: Duration,
) -> (f64, String, bool, u64, u64) {
    let rhs_expr: RecExpr<Trig> = rhs.parse().unwrap();
    let expected_cost = AstSize.cost_rec(&rhs_expr) as f64;
    let (cost, best, n_proposed, n_accepted) =
        sto_simplify(lhs, n_threads, max_time, Some(expected_cost));
    let is_optimal = cost <= expected_cost;
    (cost, best.to_string(), is_optimal, n_proposed, n_accepted)
}

// ─── Main ─────────────────────────────────────────────────────────────────────

#[rustfmt::skip]
const TESTS: &[(&str, &str)] = &[
    ("(* (* (sin t) (cos t)) (+ (tan t) (cot t)))", "1"),
    ("(- (pow (sin t) 4) (pow (cos t) 4))", "(- (* 2 (pow (sin t) 2)) 1)"),
    ("(+ (- (pow (sin t) 4) (pow (cos t) 4)) 1)", "(* 2 (pow (sin t) 2))"),
    ("(- (pow (cos t) 4) (pow (sin t) 4))", "(- (* 2 (pow (cos t) 2)) 1)"),
    ("(* (* (sin a) (cos a)) (- (tan a) (cot a)))", "(- (* 2 (pow (sin a) 2)) 1)"),
    ("(+ (pow (+ (cos A) (sin A)) 2) (pow (- (cos A) (sin A)) 2))", "2"),
    ("(+ (pow (+ 1 (tan t)) 2) (pow (- 1 (tan t)) 2))", "(* 2 (pow (sec t) 2))"),
    ("(+ (/ 1 (+ 1 (cos A))) (/ 1 (- 1 (cos A))))", "(* 2 (pow (csc A) 2))"),
    ("(/ (+ 1 (cos t)) (- 1 (cos t)))", "(pow (+ (cot t) (csc t)) 2)"),
    ("(- (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))", "(* 2 (* (tan A) (sec A)))"),
    ("(+ (/ 1 (- 1 (cos A))) (/ 1 (+ 1 (cos A))))", "(* 2 (* (cot A) (csc A)))"),
    ("(* (+ (+ 1 (sec A)) (tan A)) (+ (- 1 (csc A)) (cot A)))", "2"),
    ("(+ (/ (cos A) (+ 1 (sin A))) (/ (cos A) (- 1 (sin A))))", "(* 2 (sec A))"),
    ("(+ (/ 1 (- 1 (sin A))) (/ 1 (+ 1 (sin A))))", "(* 2 (pow (sec A) 2))"),
    ("(+ (/ 1 (+ (sin A) (cos A))) (/ 1 (- (sin A) (cos A))))", "(/ (* 2 (sin A)) (- 1 (pow (cos A) 2)))"),
    ("(/ (+ 1 (sin t)) (- 1 (sin t)))", "(pow (+ (sec t) (tan t)) 2)"),
    ("(+ (/ (cos t) (+ 1 (sin t))) (/ (+ 1 (sin t)) (cos t)))", "(* 2 (sec t))"),
    ("(+ (/ (sin A) (+ 1 (cos A))) (/ (+ 1 (cos A)) (sin A)))", "(* 2 (csc A))"),
    ("(* (* (+ 1 (cos t)) (- 1 (cos t))) (+ 1 (pow (cot t) 2)))", "1"),
    ("(* (* (+ 1 (pow (tan A) 2)) (sin A)) (cos A))", "(tan A)"),
    ("(/ (- (pow (sin b) 2) (pow (sin a) 2)) (* (pow (sin a) 2) (pow (sin b) 2)))", "(+ (pow (cot a) 2) (pow (cot b) 2))"),
    ("(/ (csc A) (+ (tan A) (cot A)))", "(cos A)"),
    ("(+ (+ (pow (tan t) 2) (pow (cot t) 2)) 2)", "(* (pow (sec t) 2) (pow (csc t) 2))"),
    ("(+ (- (pow (csc t) 4) (* 2 (pow (csc t) 2))) (- (* 2 (pow (sec t) 2)) (pow (sec t) 4)))", "(- (pow (cot t) 4) (pow (tan t) 4))"),
    ("(/ (- (sin A) (* 2 (pow (sin A) 3))) (- (* 2 (pow (cos A) 3)) (cos A)))", "(tan A)"),
    ("(+ (/ (cos t) (+ (csc t) 1)) (/ (cos t) (- (csc t) 1)))", "(* 2 (tan t))"),
    ("(+ (/ (cos t) (- 1 (tan t))) (/ (sin t) (- 1 (cot t))))", "(+ (sin t) (cos t))"),
    ("(+ (/ (tan t) (+ (sec t) 1)) (/ (tan t) (- (sec t) 1)))", "(* 2 (csc t))"),
    ("(* (- (+ (sec t) (tan t)) 1) (+ (- (sec t) (tan t)) 1))", "(* 2 (tan t))"),
    ("(/ (+ (tan A) (cot B)) (+ (cot A) (tan B)))", "(/ (tan A) (tan B))"),
    ("(/ (- (+ (tan A) (sec A)) 1) (+ (- (tan A) (sec A)) 1))", "(/ (+ 1 (sin A)) (cos A))"),
    ("(- (/ (+ 1 (sin a)) (- (csc a) (cot a))) (/ (- 1 (sin a)) (+ (csc a) (cot a))))", "(* 2 (+ 1 (cot a)))"),
    ("(+ (/ 1 (- (+ (cos t) (sin t)) 1)) (/ 1 (+ (+ (cos t) (sin t)) 1)))", "(+ (sec t) (csc t))"),
    ("(+ (/ (tan A) (- 1 (cot A))) (/ (cot A) (- 1 (tan A))))", "(+ 1 (* (sec A) (csc A)))"),
    ("(- (pow (- (sec x) 1) 2) (pow (- (tan x) (sin x)) 2))", "(pow (- 1 (cos x)) 2)"),
];

/// Trig identity simplification benchmark.
#[derive(Parser)]
struct Cli {
    /// Run EqSat tests
    #[arg(long)]
    eq: bool,

    /// Run stochastic tests
    #[arg(long)]
    sto: bool,

    /// Number of threads (cores) for stochastic search.
    /// Defaults to (available_parallelism - 2), minimum 1.
    #[arg(long, short = 'j', alias = "threads")]
    nproc: Option<usize>,

    /// Time limit in seconds for each benchmark problem
    #[arg(long, default_value_t = 10)]
    max_time: u64,

    /// Output CSV file path (default: trig_results.csv).
    /// When --sto is used the CSV matches the Lisp format:
    ///   name,time,solved,cost,#proposals,#accepted
    #[arg(long, short = 'o', default_value = "trig_results.csv")]
    output: String,

    /// Test indices (0-based). If omitted, all tests are run.
    tests: Vec<usize>,
}

fn main() {
    let cli = Cli::parse();

    if !cli.eq && !cli.sto {
        eprintln!("error: specify at least one of --eq or --sto");
        std::process::exit(1);
    }

    let run_eq = cli.eq;
    let run_sto = cli.sto;

    let avail = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let n_threads = cli.nproc.unwrap_or(avail.saturating_sub(2).max(1));
    assert!(n_threads >= 1, "--nproc must be at least 1");

    let max_time = Duration::from_secs(cli.max_time);

    // Collect (original_index, lhs, rhs) for selected tests
    let active_tests: Vec<(usize, &str, &str)> = if cli.tests.is_empty() {
        TESTS
            .iter()
            .enumerate()
            .map(|(i, (l, r))| (i, *l, *r))
            .collect()
    } else {
        cli.tests
            .iter()
            .map(|&idx| {
                assert!(
                    idx < TESTS.len(),
                    "test index {idx} out of range (0..{})",
                    TESTS.len()
                );
                (idx, TESTS[idx].0, TESTS[idx].1)
            })
            .collect()
    };

    if active_tests.is_empty() {
        eprintln!("No tests matched the given filters.");
        std::process::exit(1);
    }

    let mut eqsat_passed = 0usize;
    let mut eqsat_total = 0usize;
    let mut sto_passed = 0usize;
    let mut sto_total = 0usize;

    struct EqResult {
        cost: usize,
        expr: String,
        optimal: bool,
    }
    struct StoResult {
        time_secs: f64,
        cost: f64,
        expr: String,
        optimal: bool,
        n_proposed: u64,
        n_accepted: u64,
    }

    let mut eq_results: Vec<Option<EqResult>> = (0..active_tests.len()).map(|_| None).collect();
    let mut sto_results: Vec<Option<StoResult>> = (0..active_tests.len()).map(|_| None).collect();

    // Run eqsat tests serially
    if run_eq {
        for (i, &(idx, lhs, rhs)) in active_tests.iter().enumerate() {
            print!("{idx} eqsat ... ");
            let (cost, expr, optimal) = run_eqsat_test(lhs, rhs);
            if optimal {
                eqsat_passed += 1;
                println!("ok (cost {cost})");
            } else {
                println!("FAIL (cost {cost}, got: {expr})");
            }
            eqsat_total += 1;
            eq_results[i] = Some(EqResult {
                cost,
                expr,
                optimal,
            });
        }
    }

    // Run sto tests serially
    if run_sto {
        for (i, &(idx, lhs, rhs)) in active_tests.iter().enumerate() {
            print!("{idx} sto   ... ");
            let t0 = std::time::Instant::now();
            let (cost, expr, optimal, n_proposed, n_accepted) =
                run_sto_test(lhs, rhs, n_threads, max_time);
            let elapsed = t0.elapsed().as_secs_f64();
            if optimal {
                sto_passed += 1;
                println!("ok (cost {cost})");
            } else {
                println!("FAIL (cost {cost}, got: {expr})");
            }
            sto_total += 1;
            sto_results[i] = Some(StoResult {
                time_secs: elapsed,
                cost,
                expr,
                optimal,
                n_proposed,
                n_accepted,
            });
        }
    }

    println!();
    if run_eq {
        println!("eqsat: {eqsat_passed}/{eqsat_total} passed");
    }
    if run_sto {
        println!("sto:   {sto_passed}/{sto_total} passed");
    }

    // Build CSV
    // When --sto is the only mode, emit the Lisp-compatible format:
    //   name,time,solved,cost,#proposals,#accepted
    // Otherwise fall back to the combined/eqsat-only format.
    let csv = if run_sto && !run_eq {
        let mut rows = vec!["name,time,solved,cost,#proposals,#accepted,expr".to_string()];
        for (i, &(idx, _, _)) in active_tests.iter().enumerate() {
            if let Some(s) = &sto_results[i] {
                rows.push(format!(
                    "trig-{},{:.3},{},{},{},{},\"{}\"",
                    idx + 1,
                    s.time_secs,
                    if s.optimal { "yes" } else { "no" },
                    s.cost,
                    s.n_proposed,
                    s.n_accepted,
                    s.expr.replace('"', "\"\"")
                ));
            }
        }
        rows.join("\n")
    } else {
        // Combined or eqsat-only: legacy format
        let mut rows: Vec<String> = Vec::new();
        if run_eq && run_sto {
            rows.push(
                "index,eqsat_cost,eqsat_expr,eqsat_optimal,sto_cost,sto_expr,sto_optimal,#proposals,#accepted"
                    .to_string(),
            );
        } else if run_eq {
            rows.push("index,eqsat_cost,eqsat_expr,eqsat_optimal".to_string());
        } else {
            rows.push("index,sto_cost,sto_expr,sto_optimal,#proposals,#accepted".to_string());
        }
        for (i, &(idx, _, _)) in active_tests.iter().enumerate() {
            let eq = &eq_results[i];
            let sto = &sto_results[i];
            match (eq, sto) {
                (Some(e), Some(s)) => {
                    let eq_escaped = e.expr.replace('"', "\"\"");
                    let sto_escaped = s.expr.replace('"', "\"\"");
                    rows.push(format!(
                        "{idx},{},\"{eq_escaped}\",{},{},\"{sto_escaped}\",{},{},{}",
                        e.cost, e.optimal, s.cost, s.optimal, s.n_proposed, s.n_accepted,
                    ));
                }
                (Some(e), None) => {
                    let eq_escaped = e.expr.replace('"', "\"\"");
                    rows.push(format!("{idx},{},\"{eq_escaped}\",{}", e.cost, e.optimal));
                }
                (None, Some(s)) => {
                    let sto_escaped = s.expr.replace('"', "\"\"");
                    rows.push(format!(
                        "{idx},{},\"{sto_escaped}\",{},{},{}",
                        s.cost, s.optimal, s.n_proposed, s.n_accepted,
                    ));
                }
                (None, None) => {}
            }
        }
        rows.join("\n")
    };

    std::fs::write(&cli.output, csv).expect("failed to write output CSV");
    println!("Results saved to {}", cli.output);
}
