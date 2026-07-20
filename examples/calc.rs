//! The `cata` module's hello-world: evaluate (and pretty-print, and size)
//! boxed arithmetic expressions.  Everything below the `====` line is what
//! a consumer writes; a future `#[derive(Recursive)]` would delete the
//! section marked BOILERPLATE.

use affine_cat::cata::{at_any, pair, FoldAlg, Recursive};

// ---- the consumer's IR ----
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

// readable constructors for the demo
fn lit(n: i64) -> Expr {
    Expr::Lit(n)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}
fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Mul(Box::new(a), Box::new(b))
}

// ==== BOILERPLATE (derive-target): pattern functor + unzip + driver ====

/// One level of Expr with children replaced by `T`; payloads borrowed.
enum ExprLayer<'a, T> {
    Lit(&'a i64),
    Add(T, T),
    Mul(T, T),
}

impl Recursive for Expr {
    type Layer<'a, T> = ExprLayer<'a, T>;
    fn unzip<'a, A, B>(l: ExprLayer<'a, (A, B)>) -> (ExprLayer<'a, A>, ExprLayer<'a, B>)
    where
        Self: 'a,
    {
        match l {
            ExprLayer::Lit(n) => (ExprLayer::Lit(n), ExprLayer::Lit(n)),
            ExprLayer::Add((a1, a2), (b1, b2)) => (ExprLayer::Add(a1, b1), ExprLayer::Add(a2, b2)),
            ExprLayer::Mul((a1, a2), (b1, b2)) => (ExprLayer::Mul(a1, b1), ExprLayer::Mul(a2, b2)),
        }
    }
}

/// The per-IR driver. No binders in arithmetic, so no scope motion:
/// this is the whole bracketed skeleton for this IR.
fn fold<Env: ?Sized, A: FoldAlg<Expr, Env> + ?Sized>(a: &A, env: &Env, e: &Expr) -> A::Out {
    match e {
        Expr::Lit(n) => a.reduce(env, ExprLayer::Lit(n)),
        Expr::Add(x, y) => {
            let x = fold(a, env, x);
            let y = fold(a, env, y);
            a.reduce(env, ExprLayer::Add(x, y))
        }
        Expr::Mul(x, y) => {
            let x = fold(a, env, x);
            let y = fold(a, env, y);
            a.reduce(env, ExprLayer::Mul(x, y))
        }
    }
}

// ==== PAYLOAD: the passes themselves, one match each ====

struct Eval;
impl FoldAlg<Expr, ()> for Eval {
    type Out = i64;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, i64>) -> i64
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(n) => *n,
            ExprLayer::Add(a, b) => a + b,
            ExprLayer::Mul(a, b) => a * b,
        }
    }
}

struct Show;
impl FoldAlg<Expr, ()> for Show {
    type Out = String;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, String>) -> String
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(n) => n.to_string(),
            ExprLayer::Add(a, b) => format!("({a} + {b})"),
            ExprLayer::Mul(a, b) => format!("({a} * {b})"),
        }
    }
}

fn main() {
    // (1 + 2*3) * (4 + 5)
    let e = mul(add(lit(1), mul(lit(2), lit(3))), add(lit(4), lit(5)));

    // one pass:
    assert_eq!(fold(&Eval, &(), &e), 63);

    // two passes, ONE traversal (banana-split):
    let (v, s) = fold(&Eval.pair(Show), &(), &e);
    println!("{s} = {v}");

    // weakening: the same algebras run unchanged at any environment
    let (v2, _) = fold(&pair(at_any(Eval), at_any(Show)), &"unused env", &e);
    assert_eq!(v2, 63);

    // the erased face: a runtime-chosen pass (pass-manager shape)
    let pass: Box<dyn FoldAlg<Expr, (), Out = i64>> = Box::new(Eval);
    assert_eq!(fold(pass.as_ref(), &(), &e), 63);

    println!("ok");
}
