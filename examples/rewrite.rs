//! The transformation family: a constant-folding REWRITE via into_fold.
//! Payloads are MOVED (the non-Clone Tag proves zero duplication), and
//! the identity rewrite doubles as an embed check.
use affine_cat::cata::{FoldAlg, IntoFoldAlg, Pair, PairOwned, Rebuild};
use affine_cat_derive::Recursive;

pub struct Tag(pub String); // deliberately not Clone

#[derive(Recursive)]
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
    Note(Tag, Box<Expr>),
}

fn lit(n: i64) -> Expr {
    Expr::Lit(n)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}

/// Constant folding: Add(Lit, Lit) -> Lit; everything else rebuilt,
/// payloads reused by move.
struct ConstFold;
impl IntoFoldAlg<Expr, ()> for ConstFold {
    type Out = Expr;
    fn reduce(&self, _: &(), l: ExprLayerOwned<Expr>) -> Expr {
        match l {
            ExprLayerOwned::Lit(n) => Expr::Lit(n),
            ExprLayerOwned::Add(Expr::Lit(a), Expr::Lit(b)) => Expr::Lit(a + b),
            ExprLayerOwned::Add(a, b) => add(a, b),
            ExprLayerOwned::Note(t, e) => Expr::Note(t, Box::new(e)), // Tag MOVED
        }
    }
}

struct Render;
impl IntoFoldAlg<Expr, ()> for Render {
    type Out = String;
    fn reduce(&self, _: &(), l: ExprLayerOwned<String>) -> String {
        match l {
            ExprLayerOwned::Lit(n) => n.to_string(),
            ExprLayerOwned::Add(a, b) => format!("({a} + {b})"),
            ExprLayerOwned::Note(Tag(t), e) => format!("{t}:{e}"),
        }
    }
}

fn expr() -> Expr {
    Expr::Note(
        Tag("k".into()),
        Box::new(add(add(lit(1), lit(2)), add(lit(3), lit(4)))),
    )
}

/// borrowed analysis: node count (reads the INPUT tree)
struct Size;
impl FoldAlg<Expr, ()> for Size {
    type Out = usize;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, usize>) -> usize
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(_) => 1,
            ExprLayer::Add(a, b) => 1 + a + b,
            ExprLayer::Note(_, e) => 1 + e,
        }
    }
}

fn main() {
    // reflection law: the identity rewrite really is the identity
    let same = expr().into_fold(&(), &Rebuild);
    assert_eq!(same.into_fold(&(), &Render), expr().into_fold(&(), &Render));

    // MIXED PAIR: rewrite + analysis, ONE consuming traversal, zero dup.
    // The analysis sees the input (size 8 pre-fold), the rewrite consumes.
    let (folded2, input_size) = expr().into_fold(&(), &PairOwned(ConstFold, Size));
    assert_eq!(input_size, 8);
    assert_eq!(folded2.into_fold(&(), &Render), "k:10");

    // copy-and-analyze law at runtime: PairOwned(Rebuild, g) = (copy, analysis)
    // nested composition across the owned/borrowed boundary: one pass,
    // one rewrite, two analyses
    let (folded3, (n1, n2)) = expr().into_fold(&(), &PairOwned(ConstFold, Pair(Size, Size)));
    assert_eq!((n1, n2), (8, 8));
    assert_eq!(folded3.into_fold(&(), &Render), "k:10");

    let (copy, n) = expr().into_fold(&(), &PairOwned(Rebuild, Size));
    assert_eq!(
        (copy.into_fold(&(), &Render), n),
        (expr().into_fold(&(), &Render), 8)
    );

    let folded = expr().into_fold(&(), &ConstFold); // tree consumed, Tag moved
    let shown = folded.into_fold(&(), &Render); // consumed again
    assert_eq!(shown, "k:10"); // cascades: (1+2)->3, (3+4)->7, 3+7->10
    println!("rewrite: {shown}");
}
