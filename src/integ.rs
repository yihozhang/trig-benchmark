use clap::Parser;
use egg::stochastic::{
    PeriodicBeta, SimpleLcg, State, StoAnalysis, StoConditionalApplier, StoConfig, StoRewrite,
    StoRunner,
};
use egg::{rewrite as rw, *};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

type EGraph = egg::EGraph<Integ, ConstantFold>;
type Rewrite = egg::Rewrite<Integ, ConstantFold>;

define_language! {
    enum Integ {
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
        "ln" = Ln(Id),
        "exp" = Exp(Id),
        "arctan" = Arctan(Id),
        "arcsin" = Arcsin(Id),
        "d" = D([Id; 2]),
        "int" = Int([Id; 2]),
        Symbol(Symbol),
    }
}

#[derive(Default, Clone)]
struct ConstantFold {
    unsound: bool,
}
impl Analysis<Integ> for ConstantFold {
    type Data = Option<(i32, PatternAst<Integ>)>;

    fn make(egraph: &mut EGraph, enode: &Integ, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Integ::Num(n) => (*n, format!("{}", n).parse().unwrap()),
            Integ::Add([a, b]) => {
                let s = x(a)?.checked_add(x(b)?)?;
                (s, format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Integ::Sub([a, b]) => {
                let s = x(a)?.checked_sub(x(b)?)?;
                (s, format!("(- {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Integ::Mul([a, b]) => {
                let s = x(a)?.checked_mul(x(b)?)?;
                (s, format!("(* {} {})", x(a)?, x(b)?).parse().unwrap())
            }
            Integ::Pow([a, b]) => {
                let base = x(a)?;
                let exp = x(b)?;
                if exp < 0 {
                    if base.abs() != 1 {
                        return None;
                    }
                    // (-1)^(neg odd) = -1, (-1)^(neg even) = 1, 1^anything = 1
                    let s = if base == 1 { 1 } else if exp % 2 == 0 { 1 } else { -1 };
                    return Some((s, format!("{}", s).parse().unwrap()));
                }
                let s = base.checked_pow(exp as u32)?;
                (s, format!("(pow {} {})", base, exp).parse().unwrap())
            }
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            if a.0 != b.0 {
                self.unsound = true;
            }
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
                let added = egraph.add(Integ::Num(c));
                egraph.union(id, added);
            }
            egraph[id].nodes.retain(|n| n.is_leaf());
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn is_const(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var: Var = var.parse().unwrap();
    move |egraph, _, subst| egraph[subst[var]].data.is_some()
}

fn is_not_neg1(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var: Var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data {
            d.0 != -1
        } else {
            true
        }
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite> {
    vec![
    // ── (a+b)^2 expansion ───────────────────────────────────────────────────
    rw!("pow2";       "(pow ?a 2)" => "(* ?a ?a)"),
    rw!("i-pow2";     "(* ?a ?a)" => "(pow ?a 2)"),
    rw!("binom2";     "(pow (+ ?a ?b) 2)" =>
        "(+ (+ (pow ?a 2) (* 2 (* ?a ?b))) (pow ?b 2))"),
    rw!("i-binom2";   "(+ (+ (pow ?a 2) (* 2 (* ?a ?b))) (pow ?b 2))" =>
        "(pow (+ ?a ?b) 2)"),

    // ── Integration — linearity ──────────────────────────────────────────────
    rw!("int-add";       "(int (+ ?f ?g) ?x)" => "(+ (int ?f ?x) (int ?g ?x))"),
    rw!("int-sub";       "(int (- ?f ?g) ?x)" => "(- (int ?f ?x) (int ?g ?x))"),
    rw!("int-const-mul"; "(int (* ?c ?f) ?x)" => "(* ?c (int ?f ?x))" if is_const("?c")),
    rw!("int-const";     "(int ?c ?x)" => "(* ?c ?x)" if is_const("?c")),

    // ── Sqrt ─────────────────────────────────────────────────────────────────
    rw!("sqrt-sq";    "(pow (sqrt ?a) 2)" => "?a"),
    rw!("sq-sqrt";    "(sqrt (pow ?a 2))" => "?a"),

    // ── Integration — power rule ─────────────────────────────────────────────
    rw!("int-var";       "(int ?x ?x)" => "(/ (pow ?x 2) 2)"),
    rw!("int-pow";       "(int (pow ?x ?n) ?x)" =>
        "(/ (pow ?x (+ ?n 1)) (+ ?n 1))" if is_const("?n") if is_not_neg1("?n")),
    rw!("int-recip";     "(int (/ 1 ?x) ?x)" => "(ln ?x)"),
    rw!("int-pow-neg1";  "(int (pow ?x -1) ?x)" => "(ln ?x)"),

    // ── Commutativity and associativity ──────────────────────────────────────
    rw!("comm-add";    "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("comm-mul";    "(* ?a ?b)" => "(* ?b ?a)"),
    rw!("assoc-add";   "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
    rw!("i-assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul";   "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
    rw!("i-assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    // ── Distributivity ───────────────────────────────────────────────────────
    rw!("distribute";   "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor";       "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    rw!("factor-sub";   "(- (* ?a ?b) (* ?a ?c))" => "(* ?a (- ?b ?c))"),

    // ── Algebraic identities ─────────────────────────────────────────────────
    rw!("zero-add";    "(+ ?a 0)" => "?a"),
    rw!("one-mul";     "(* ?a 1)" => "?a"),
    rw!("zero-mul";    "(* ?a 0)" => "0"),
    rw!("cancel-sub";  "(- ?a ?a)" => "0"),
    rw!("cancel-div";  "(/ ?a ?a)" => "1"),

    // ── Subtraction and division sugar ────────────────────────────────────────
    rw!("sub-canon";   "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("i-sub-canon"; "(+ ?a (* -1 ?b))" => "(- ?a ?b)"),
    rw!("div-canon";   "(/ ?a ?b)" => "(* ?a (/ 1 ?b))"),
    rw!("i-div-canon"; "(* ?a (/ 1 ?b))" => "(/ ?a ?b)"),

    // ── Fractions ────────────────────────────────────────────────────────────
    rw!("cancel-frac";         "(/ (* ?a ?c) (* ?b ?c))" => "(/ ?a ?b)"),
    rw!("cancel-frac-simple";  "(/ (* ?a ?b) ?a)" => "?b"),
    rw!("frac-add-same-denom"; "(+ (/ ?a ?b) (/ ?c ?b))" => "(/ (+ ?a ?c) ?b)"),

    // ── Powers ───────────────────────────────────────────────────────────────
    rw!("pow0";       "(pow ?a 0)" => "1"),
    rw!("pow1";       "(pow ?a 1)" => "?a"),
    rw!("pow-mul";    "(pow (* ?a ?b) ?n)" => "(* (pow ?a ?n) (pow ?b ?n))"),
    rw!("i-pow-mul";  "(* (pow ?a ?n) (pow ?b ?n))" => "(pow (* ?a ?b) ?n)"),
    rw!("pow-div";    "(pow (/ ?a ?b) ?n)" => "(/ (pow ?a ?n) (pow ?b ?n))"),
    rw!("i-pow-div";  "(/ (pow ?a ?n) (pow ?b ?n))" => "(pow (/ ?a ?b) ?n)"),
    rw!("pow-add";    "(* (pow ?a ?m) (pow ?a ?n))" => "(pow ?a (+ ?m ?n))"),
    rw!("pow4-split"; "(pow ?a 4)" => "(* (pow ?a 2) (pow ?a 2))"),
    rw!("pow-neg";    "(pow ?a -1)" => "(/ 1 ?a)"),
    rw!("i-pow-neg";  "(/ 1 ?a)" => "(pow ?a -1)"),

    // ── Differentiation ───────────────────────────────────────────────────────
    rw!("d-const";     "(d ?c ?x)" => "0" if is_const("?c")),
    rw!("d-var";       "(d ?x ?x)" => "1"),
    rw!("d-pow";       "(d (pow ?x ?n) ?x)" => "(* ?n (pow ?x (- ?n 1)))" if is_const("?n")),
    rw!("d-const-mul"; "(d (* ?c ?f) ?x)" => "(* ?c (d ?f ?x))" if is_const("?c")),
    rw!("d-sin";       "(d (sin ?x) ?x)" => "(cos ?x)"),
    rw!("d-cos";       "(d (cos ?x) ?x)" => "(* -1 (sin ?x))"),
    rw!("d-exp";       "(d (exp ?x) ?x)" => "(exp ?x)"),
    rw!("d-ln";        "(d (ln ?x) ?x)" => "(/ 1 ?x)"),

    // ── Integration — trigonometric / exponential / logarithmic ─────────────
    rw!("int-sin";     "(int (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rw!("int-cos";     "(int (cos ?x) ?x)" => "(sin ?x)"),
    rw!("int-exp";     "(int (exp ?x) ?x)" => "(exp ?x)"),
    rw!("int-ln";      "(int (ln ?x) ?x)" => "(- (* ?x (ln ?x)) ?x)"),

    // ── Integration by parts ─────────────────────────────────────────────────
    rw!("ibp"; "(int (* ?u ?v) ?x)" =>
        "(- (* ?u (int ?v ?x)) (int (* (d ?u ?x) (int ?v ?x)) ?x))"),

    // ── Factoring ────────────────────────────────────────────────────────────
    rw!("diff-sq";    "(- (pow ?a 2) (pow ?b 2))" => "(* (+ ?a ?b) (- ?a ?b))"),
    rw!("i-diff-sq";  "(* (+ ?a ?b) (- ?a ?b))" => "(- (pow ?a 2) (pow ?b 2))"),
    rw!("diff-sq-1";  "(- (pow ?a 2) 1)" => "(* (+ ?a 1) (- ?a 1))"),
    rw!("i-diff-sq-1"; "(* (+ ?a 1) (- ?a 1))" => "(- (pow ?a 2) 1)"),
    rw!("diff-cubes"; "(- (pow ?a 3) (pow ?b 3))" =>
        "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    rw!("i-diff-cubes"; "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))" =>
        "(- (pow ?a 3) (pow ?b 3))"),
    rw!("diff-cubes-1"; "(- (pow ?a 3) 1)" =>
        "(* (- ?a 1) (+ (+ (pow ?a 2) ?a) 1))"),
    rw!("i-diff-cubes-1"; "(* (- ?a 1) (+ (+ (pow ?a 2) ?a) 1))" =>
        "(- (pow ?a 3) 1)"),
    ]
}

/// Cost function that penalises unevaluated `d` and `int` nodes so the
/// extractor strongly prefers fully-evaluated forms.
struct IntegCost;
impl CostFunction<Integ> for IntegCost {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Integ, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let base = match enode {
            Integ::D(_) | Integ::Int(_) => 100,
            _ => 1,
        };
        enode.fold(base, |sum, id| sum.saturating_add(costs(id)))
    }
}

fn simplify(s: &str) -> (usize, String, bool) {
    let expr: RecExpr<Integ> = s.parse().unwrap();

    let snapshot: Rc<RefCell<Option<(EGraph, Id)>>> =
        Rc::new(RefCell::new(None));
    let snap_ref = Rc::clone(&snapshot);

    let runner = Runner::default()
        .with_expr(&expr)
        .with_node_limit(usize::MAX)
        .with_time_limit(Duration::from_secs(10))
        .with_iter_limit(usize::MAX)
        .with_hook(move |runner: &mut Runner<Integ, ConstantFold>| {
            if runner.egraph.analysis.unsound {
                return Err("unsound merge detected".into());
            }
            *snap_ref.borrow_mut() = Some((runner.egraph.clone(), runner.roots[0]));
            Ok(())
        })
        .run(&rules());

    let root = runner.roots[0];
    let unsound = runner.egraph.analysis.unsound;

    let (best_cost, best): (usize, RecExpr<Integ>) = if unsound {
        let snap = snapshot.borrow();
        let (eg, snap_root) = snap.as_ref().expect("no snapshot before unsoundness");
        let extractor = Extractor::new(eg, IntegCost);
        extractor.find_best(*snap_root)
    } else {
        let extractor = Extractor::new(&runner.egraph, IntegCost);
        extractor.find_best(root)
    };

    println!(
        "Simplified (cost {}):\n  {} =>\n  {}",
        best_cost, expr, best
    );
    println!("{}", runner.report());
    if unsound {
        println!("WARNING: unsound merge detected, result extracted from snapshot");
    }
    (best_cost, best.to_string(), unsound)
}

fn has_int_or_d(expr: &RecExpr<Integ>) -> bool {
    expr.as_ref()
        .iter()
        .any(|n| matches!(n, Integ::Int(_) | Integ::D(_)))
}

fn run_eqsat_test(lhs: &str, rhs: &str) -> (usize, String, bool) {
    let (cost, best, _unsound) = simplify(lhs);
    let rhs_expr: RecExpr<Integ> = rhs.parse().unwrap();
    let expected_cost = IntegCost.cost_rec(&rhs_expr);
    let best_expr: RecExpr<Integ> = best.parse().unwrap();
    let is_optimal = !has_int_or_d(&best_expr) && cost <= expected_cost;
    (cost, best, is_optimal)
}

// ── Stochastic search ────────────────────────────────────────────────────────

#[derive(Default)]
struct IntegStoAnalysis;

impl StoAnalysis<Integ> for IntegStoAnalysis {
    type Data = Option<i32>;

    fn make(&self, enode: &Integ, analysis: &[Option<i32>]) -> Option<i32> {
        let x = |i: &Id| analysis[usize::from(*i)];
        match enode {
            Integ::Num(n) => Some(*n),
            Integ::Add([a, b]) => x(a)?.checked_add(x(b)?),
            Integ::Sub([a, b]) => x(a)?.checked_sub(x(b)?),
            Integ::Mul([a, b]) => x(a)?.checked_mul(x(b)?),
            Integ::Pow([a, b]) => {
                let base = x(a)?;
                let exp = x(b)?;
                if exp < 0 {
                    if base.abs() != 1 {
                        return None;
                    }
                    let s = if base == 1 { 1 } else if exp % 2 == 0 { 1 } else { -1 };
                    return Some(s);
                }
                base.checked_pow(exp as u32)
            }
            _ => None,
        }
    }

    fn cost(&self, enode: &Integ, _analysis: &[Self::Data], children_cost: &[f64]) -> f64 {
        let child_sum = enode.fold(0.0, |acc, child| acc + children_cost[usize::from(child)]);
        match enode {
            Integ::D(_) | Integ::Int(_) => 100.0 + child_sum * child_sum,
            _ => 1.0 + child_sum,
        }
    }
}

type IntegState = State<Integ, IntegStoAnalysis>;
type IntegRw = StoRewrite<Integ, IntegStoAnalysis>;

fn normalize_integ(state: &mut IntegState, _id: Id, node: Integ) -> Option<Integ> {
    let val = |id: Id| -> Option<i32> { state.analysis[usize::from(id)] };
    match node {
        Integ::Add([a, b]) => Some(Integ::Num(val(a)?.checked_add(val(b)?)?)),
        Integ::Sub([a, b]) => Some(Integ::Num(val(a)?.checked_sub(val(b)?)?)),
        Integ::Mul([a, b]) => Some(Integ::Num(val(a)?.checked_mul(val(b)?)?)),
        Integ::Pow([a, b]) => {
            let base = val(a)?;
            let exp = val(b)?;
            if exp < 0 {
                if base.abs() != 1 {
                    return None;
                }
                let s = if base == 1 { 1 } else if exp % 2 == 0 { 1 } else { -1 };
                return Some(Integ::Num(s));
            }
            Some(Integ::Num(base.checked_pow(exp as u32)?))
        }
        _ => None,
    }
}

fn p_integ(s: &str) -> Pattern<Integ> {
    s.parse().unwrap()
}

fn sto_rw(name: &str, lhs: &str, rhs: &str) -> IntegRw {
    StoRewrite::new(name, p_integ(lhs), p_integ(rhs)).unwrap()
}

fn sto_rw_if(
    name: &str,
    lhs: &str,
    rhs: &str,
    cond: impl Fn(&IntegState, Id, &Subst) -> bool + Send + Sync + 'static,
) -> IntegRw {
    StoRewrite::new(
        name,
        p_integ(lhs),
        StoConditionalApplier {
            applier: Arc::new(p_integ(rhs)),
            condition: Box::new(cond),
        },
    )
    .unwrap()
}


fn sto_is_const(var: &str) -> impl Fn(&IntegState, Id, &Subst) -> bool + Send + Sync + 'static {
    let v: Var = var.parse().unwrap();
    move |s: &IntegState, _: Id, subst: &Subst| matches!(s.rec_expr[subst[v]], Integ::Num(_))
}

fn sto_is_not_neg1(var: &str) -> impl Fn(&IntegState, Id, &Subst) -> bool + Send + Sync + 'static {
    let v: Var = var.parse().unwrap();
    move |s: &IntegState, _: Id, subst: &Subst| {
        match s.rec_expr[subst[v]] {
            Integ::Num(n) => n != -1,
            _ => true,
        }
    }
}

#[rustfmt::skip]
fn sto_rules() -> Vec<IntegRw> {
    vec![
    // ── (a+b)^2 expansion ───────────────────────────────────────────────────
    sto_rw("pow2",       "(pow ?a 2)", "(* ?a ?a)"),
    sto_rw("i-pow2",     "(* ?a ?a)", "(pow ?a 2)"),
    sto_rw("binom2",     "(pow (+ ?a ?b) 2)",
        "(+ (+ (pow ?a 2) (* 2 (* ?a ?b))) (pow ?b 2))"),
    sto_rw("i-binom2",   "(+ (+ (pow ?a 2) (* 2 (* ?a ?b))) (pow ?b 2))",
        "(pow (+ ?a ?b) 2)"),

    // ── Integration — linearity ──────────────────────────────────────────────
    sto_rw("int-add",       "(int (+ ?f ?g) ?x)", "(+ (int ?f ?x) (int ?g ?x))"),
    sto_rw("int-sub",       "(int (- ?f ?g) ?x)", "(- (int ?f ?x) (int ?g ?x))"),
    sto_rw_if("int-const-mul", "(int (* ?c ?f) ?x)", "(* ?c (int ?f ?x))", sto_is_const("?c")),
    sto_rw_if("int-const",     "(int ?c ?x)",        "(* ?c ?x)",          sto_is_const("?c")),

    // ── Sqrt ─────────────────────────────────────────────────────────────────
    sto_rw("sqrt-sq",    "(pow (sqrt ?a) 2)", "?a"),
    sto_rw("sq-sqrt",    "(sqrt (pow ?a 2))", "?a"),

    // ── Integration — power rule ─────────────────────────────────────────────
    sto_rw("int-var",       "(int ?x ?x)", "(/ (pow ?x 2) 2)"),
    sto_rw_if("int-pow", "(int (pow ?x ?n) ?x)", "(/ (pow ?x (+ ?n 1)) (+ ?n 1))", {
        let c = sto_is_const("?n");
        let n = sto_is_not_neg1("?n");
        move |s, pos, subst| c(s, pos, subst) && n(s, pos, subst)
    }),
    sto_rw("int-recip",     "(int (/ 1 ?x) ?x)", "(ln ?x)"),
    sto_rw("int-pow-neg1",  "(int (pow ?x -1) ?x)", "(ln ?x)"),

    // ── Commutativity and associativity ──────────────────────────────────────
    sto_rw("comm-add",    "(+ ?a ?b)", "(+ ?b ?a)"),
    sto_rw("comm-mul",    "(* ?a ?b)", "(* ?b ?a)"),
    sto_rw("assoc-add",   "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),
    sto_rw("i-assoc-add", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)"),
    sto_rw("assoc-mul",   "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))"),
    sto_rw("i-assoc-mul", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)"),

    // ── Distributivity ───────────────────────────────────────────────────────
    sto_rw("distribute",   "(* ?a (+ ?b ?c))", "(+ (* ?a ?b) (* ?a ?c))"),
    sto_rw("factor",       "(+ (* ?a ?b) (* ?a ?c))", "(* ?a (+ ?b ?c))"),
    sto_rw("factor-sub",   "(- (* ?a ?b) (* ?a ?c))", "(* ?a (- ?b ?c))"),

    // ── Algebraic identities ─────────────────────────────────────────────────
    sto_rw("zero-add",    "(+ ?a 0)", "?a"),
    sto_rw("one-mul",     "(* ?a 1)", "?a"),
    sto_rw("zero-mul",    "(* ?a 0)", "0"),
    sto_rw("cancel-sub",  "(- ?a ?a)", "0"),
    sto_rw("cancel-div",  "(/ ?a ?a)", "1"),

    // ── Subtraction and division sugar ────────────────────────────────────────
    sto_rw("sub-canon",   "(- ?a ?b)", "(+ ?a (* -1 ?b))"),
    sto_rw("i-sub-canon", "(+ ?a (* -1 ?b))", "(- ?a ?b)"),
    sto_rw("div-canon",   "(/ ?a ?b)", "(* ?a (/ 1 ?b))"),
    sto_rw("i-div-canon", "(* ?a (/ 1 ?b))", "(/ ?a ?b)"),

    // ── Fractions ────────────────────────────────────────────────────────────
    sto_rw("cancel-frac",         "(/ (* ?a ?c) (* ?b ?c))", "(/ ?a ?b)"),
    sto_rw("cancel-frac-simple",  "(/ (* ?a ?b) ?a)", "?b"),
    sto_rw("frac-add-same-denom", "(+ (/ ?a ?b) (/ ?c ?b))", "(/ (+ ?a ?c) ?b)"),

    // ── Powers ───────────────────────────────────────────────────────────────
    sto_rw("pow0",       "(pow ?a 0)", "1"),
    sto_rw("pow1",       "(pow ?a 1)", "?a"),
    sto_rw("pow-mul",    "(pow (* ?a ?b) ?n)", "(* (pow ?a ?n) (pow ?b ?n))"),
    sto_rw("i-pow-mul",  "(* (pow ?a ?n) (pow ?b ?n))", "(pow (* ?a ?b) ?n)"),
    sto_rw("pow-div",    "(pow (/ ?a ?b) ?n)", "(/ (pow ?a ?n) (pow ?b ?n))"),
    sto_rw("i-pow-div",  "(/ (pow ?a ?n) (pow ?b ?n))", "(pow (/ ?a ?b) ?n)"),
    sto_rw("pow-add",    "(* (pow ?a ?m) (pow ?a ?n))", "(pow ?a (+ ?m ?n))"),
    sto_rw("pow4-split", "(pow ?a 4)", "(* (pow ?a 2) (pow ?a 2))"),
    sto_rw("pow-neg",    "(pow ?a -1)", "(/ 1 ?a)"),
    sto_rw("i-pow-neg",  "(/ 1 ?a)", "(pow ?a -1)"),

    // ── Differentiation ───────────────────────────────────────────────────────
    sto_rw_if("d-const",     "(d ?c ?x)",         "0",                          sto_is_const("?c")),
    sto_rw("d-var",       "(d ?x ?x)", "1"),
    sto_rw_if("d-pow",       "(d (pow ?x ?n) ?x)", "(* ?n (pow ?x (- ?n 1)))", sto_is_const("?n")),
    sto_rw_if("d-const-mul", "(d (* ?c ?f) ?x)",   "(* ?c (d ?f ?x))",         sto_is_const("?c")),
    sto_rw("d-sin",       "(d (sin ?x) ?x)", "(cos ?x)"),
    sto_rw("d-cos",       "(d (cos ?x) ?x)", "(* -1 (sin ?x))"),
    sto_rw("d-exp",       "(d (exp ?x) ?x)", "(exp ?x)"),
    sto_rw("d-ln",        "(d (ln ?x) ?x)", "(/ 1 ?x)"),

    // ── Integration — trigonometric / exponential / logarithmic ─────────────
    sto_rw("int-sin",     "(int (sin ?x) ?x)", "(* -1 (cos ?x))"),
    sto_rw("int-cos",     "(int (cos ?x) ?x)", "(sin ?x)"),
    sto_rw("int-exp",     "(int (exp ?x) ?x)", "(exp ?x)"),
    sto_rw("int-ln",      "(int (ln ?x) ?x)", "(- (* ?x (ln ?x)) ?x)"),

    // ── Integration by parts ─────────────────────────────────────────────────
    sto_rw("ibp", "(int (* ?u ?v) ?x)",
        "(- (* ?u (int ?v ?x)) (int (* (d ?u ?x) (int ?v ?x)) ?x))"),

    // ── Factoring ────────────────────────────────────────────────────────────
    sto_rw("diff-sq",    "(- (pow ?a 2) (pow ?b 2))", "(* (+ ?a ?b) (- ?a ?b))"),
    sto_rw("i-diff-sq",  "(* (+ ?a ?b) (- ?a ?b))", "(- (pow ?a 2) (pow ?b 2))"),
    sto_rw("diff-sq-1",  "(- (pow ?a 2) 1)", "(* (+ ?a 1) (- ?a 1))"),
    sto_rw("i-diff-sq-1", "(* (+ ?a 1) (- ?a 1))", "(- (pow ?a 2) 1)"),
    sto_rw("diff-cubes", "(- (pow ?a 3) (pow ?b 3))",
        "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))"),
    sto_rw("i-diff-cubes", "(* (- ?a ?b) (+ (+ (pow ?a 2) (* ?a ?b)) (pow ?b 2)))",
        "(- (pow ?a 3) (pow ?b 3))"),
    sto_rw("diff-cubes-1", "(- (pow ?a 3) 1)",
        "(* (- ?a 1) (+ (+ (pow ?a 2) ?a) 1))"),
    sto_rw("i-diff-cubes-1", "(* (- ?a 1) (+ (+ (pow ?a 2) ?a) 1))",
        "(- (pow ?a 3) 1)"),
    ]
}

fn sto_simplify(s: &str, n_threads: usize) -> (f64, RecExpr<Integ>) {
    let timeout = Duration::from_secs(10);
    let initial_expr: Arc<RecExpr<Integ>> = Arc::new(s.parse().unwrap());

    let handles: Vec<_> = (0..n_threads)
        .map(|i| {
            let initial_expr = Arc::clone(&initial_expr);
            let seed = 42u64 + i as u64;
            std::thread::spawn(move || {
                let mut runner =
                    StoRunner::new((*initial_expr).clone(), sto_rules())
                        .with_normalizer(normalize_integ);
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

fn sto_has_int_or_d(expr: &RecExpr<Integ>) -> bool {
    expr.as_ref()
        .iter()
        .any(|n| matches!(n, Integ::Int(_) | Integ::D(_)))
}

fn run_sto_test(lhs: &str, rhs: &str, n_threads: usize) -> (f64, String, bool) {
    let (cost, best) = sto_simplify(lhs, n_threads);
    let rhs_expr: RecExpr<Integ> = rhs.parse().unwrap();
    let expected_cost = IntegCost.cost_rec(&rhs_expr) as f64;
    let is_optimal = !sto_has_int_or_d(&best) && cost <= expected_cost;
    (cost, best.to_string(), is_optimal)
}

// ─── Main ─────────────────────────────────────────────────────────────────────

const TESTS: &[(&str, &str)] = &[
    // ∫(x²+1)²/x² dx
    ("(int (/ (pow (+ (pow x 2) 1) 2) (pow x 2)) x)", "(+ (/ (pow x 3) 3) (- (* 2 x) (/ 1 x)))"),
    // ∫(√x + 1/√x)² dx
    ("(int (pow (+ (sqrt x) (/ 1 (sqrt x))) 2) x)", "(+ (/ (pow x 2) 2) (+ (* 2 x) (ln x)))"),
    // ∫(x⁴−1)/(x²+1) dx
    ("(int (/ (- (pow x 4) 1) (+ (pow x 2) 1)) x)", "(- (/ (pow x 3) 3) x)"),
    // ∫(x³−1)/(x−1) dx
    ("(int (/ (- (pow x 3) 1) (- x 1)) x)", "(+ (/ (pow x 3) 3) (+ (/ (pow x 2) 2) x))"),
    // ∫(x²+1)/(x−1)² dx
    ("(int (/ (+ (pow x 2) 1) (pow (- x 1) 2)) x)", "(+ x (+ (* 2 (ln (- x 1))) (/ -2 (- x 1))))"),
    // ∫x²·sin(x) dx
    ("(int (* (pow x 2) (sin x)) x)", "(+ (* -1 (* (pow x 2) (cos x))) (- (* 2 (* x (sin x))) (* -2 (cos x))))"),
    // ∫x²·eˣ dx
    ("(int (* (pow x 2) (exp x)) x)", "(* (exp x) (+ (- (pow x 2) (* 2 x)) 2))"),
    // ∫x·cos(x) dx
    ("(int (* x (cos x)) x)", "(+ (* x (sin x)) (cos x))"),
    // ∫x³·ln(x) dx
    ("(int (* (pow x 3) (ln x)) x)", "(- (/ (* (pow x 4) (ln x)) 4) (/ (pow x 4) 16))"),
    // ∫(ln(x))² dx
    ("(int (pow (ln x) 2) x)", "(+ (- (* x (pow (ln x) 2)) (* 2 (* x (ln x)))) (* 2 x))"),
];

/// Integration benchmark.
///
/// Specify --eq and/or --sto to select which modes to run.
/// Optionally pass test indices (0-based) to run a subset.
/// With no indices, all tests are run for the selected mode(s).
#[derive(Parser)]
struct Cli {
    /// Run EqSat tests
    #[arg(long)]
    eq: bool,

    /// Run stochastic tests
    #[arg(long)]
    sto: bool,

    /// Number of threads for stochastic search
    #[arg(short = 'j')]
    threads: Option<usize>,

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
    // NOTE: By default we leave 2 threads free to maintain system responsiveness while running
    let n_threads = cli.threads.unwrap_or(avail.saturating_sub(2).max(1));
    assert!(
        n_threads <= avail,
        "-j {n_threads} exceeds available parallelism ({avail})"
    );

    // Collect (original_index, lhs, rhs) for selected tests
    let active_tests: Vec<(usize, &str, &str)> = if cli.tests.is_empty() {
        TESTS.iter().enumerate().map(|(i, (l, r))| (i, *l, *r)).collect()
    } else {
        cli.tests
            .iter()
            .map(|&idx| {
                assert!(idx < TESTS.len(), "test index {idx} out of range (0..{})", TESTS.len());
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
    let mut rows: Vec<String> = Vec::new();
    if run_eq && run_sto {
        rows.push(
            "index,eqsat_cost,eqsat_expr,eqsat_optimal,sto_cost,sto_expr,sto_optimal".to_string(),
        );
    } else if run_eq {
        rows.push("index,eqsat_cost,eqsat_expr,eqsat_optimal".to_string());
    } else {
        rows.push("index,sto_cost,sto_expr,sto_optimal".to_string());
    }

    struct EqResult {
        cost: usize,
        expr: String,
        optimal: bool,
    }
    struct StoResult {
        cost: f64,
        expr: String,
        optimal: bool,
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
            eq_results[i] = Some(EqResult { cost, expr, optimal });
        }
    }

    // Run sto tests serially
    if run_sto {
        for (i, &(idx, lhs, rhs)) in active_tests.iter().enumerate() {
            print!("{idx} sto   ... ");
            let (cost, expr, optimal) = run_sto_test(lhs, rhs, n_threads);
            if optimal {
                sto_passed += 1;
                println!("ok (cost {cost})");
            } else {
                println!("FAIL (cost {cost}, got: {expr})");
            }
            sto_total += 1;
            sto_results[i] = Some(StoResult { cost, expr, optimal });
        }
    }

    // Build CSV rows
    for (i, &(idx, _, _)) in active_tests.iter().enumerate() {
        let eq = &eq_results[i];
        let sto = &sto_results[i];
        match (eq, sto) {
            (Some(e), Some(s)) => {
                let eq_escaped = e.expr.replace('"', "\"\"");
                let sto_escaped = s.expr.replace('"', "\"\"");
                rows.push(format!(
                    "{idx},{},\"{eq_escaped}\",{},{},\"{sto_escaped}\",{}",
                    e.cost, e.optimal, s.cost, s.optimal
                ));
            }
            (Some(e), None) => {
                let eq_escaped = e.expr.replace('"', "\"\"");
                rows.push(format!(
                    "{idx},{},\"{eq_escaped}\",{}",
                    e.cost, e.optimal
                ));
            }
            (None, Some(s)) => {
                let sto_escaped = s.expr.replace('"', "\"\"");
                rows.push(format!(
                    "{idx},{},\"{sto_escaped}\",{}",
                    s.cost, s.optimal
                ));
            }
            (None, None) => {}
        }
    }

    println!();
    if run_eq {
        println!("eqsat: {eqsat_passed}/{eqsat_total} passed");
    }
    if run_sto {
        println!("sto:   {sto_passed}/{sto_total} passed");
    }

    let csv = rows.join("\n");
    std::fs::write("integ_results.csv", csv).expect("failed to write integ_results.csv");
    println!("Results saved to integ_results.csv");
}
