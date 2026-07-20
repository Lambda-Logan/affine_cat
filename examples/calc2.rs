//! Borrowed-edition derive: the fold lends payloads (&'a P) — no Clone,
//! no Comonoid, the tree survives, Pair works on NON-duplicable payloads,
//! and custom pointer types are holes via a 15-line Holes impl.
use affine_cat::cata::FoldAlg;
use affine_cat::deref_holes;
use affine_cat_derive::Recursive;

// A user's own pointer type: implement Deref, invoke the macro, done —
// the derive accepts it as a hole with no further ceremony.
pub struct P<T>(Box<T>);
impl<T> std::ops::Deref for P<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
deref_holes! { [T] P<T> }

#[derive(Recursive)]
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
    Neg(P<Expr>),                    // custom pointer hole
    Sum(Vec<Expr>),                  // n-ary hole
    Note(String, Option<Box<Expr>>), // borrowed payload + optional hole
}

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
            ExprLayer::Neg(a) => -a,
            ExprLayer::Sum(xs) => xs.into_iter().sum(),
            ExprLayer::Note(_, e) => e.unwrap_or(0),
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
            ExprLayer::Neg(a) => format!("-{a}"),
            ExprLayer::Sum(xs) => format!("sum[{}]", xs.join(", ")),
            // keeping the payload is the algebra's decision, paid here:
            ExprLayer::Note(s, e) => format!("{s}:{}", e.unwrap_or_default()),
        }
    }
}

// The Comonoid cliffhanger, resolved: a payload with NO Clone impl,
// folded with Pair — both algebras receive &Opaque, nothing duplicates.
pub struct Opaque(pub u8);

#[derive(Recursive)]
enum Tagged {
    Tip(Opaque),
    Two(Box<Tagged>, Box<Tagged>),
}

struct Count;
impl FoldAlg<Tagged, ()> for Count {
    type Out = usize;
    fn reduce<'a>(&self, _: &(), l: TaggedLayer<'a, usize>) -> usize
    where
        Tagged: 'a,
    {
        match l {
            TaggedLayer::Tip(_) => 1,
            TaggedLayer::Two(a, b) => a + b,
        }
    }
}
struct MaxTag;
impl FoldAlg<Tagged, ()> for MaxTag {
    type Out = u8;
    fn reduce<'a>(&self, _: &(), l: TaggedLayer<'a, u8>) -> u8
    where
        Tagged: 'a,
    {
        match l {
            TaggedLayer::Tip(o) => o.0,
            TaggedLayer::Two(a, b) => a.max(b),
        }
    }
}

fn main() {
    let lit = |n| Expr::Lit(n);
    let add = |a, b| Expr::Add(Box::new(a), Box::new(b));

    // note:"x" (-(1 + 2) + sum[3, 4])
    let e = Expr::Note(
        "x".into(),
        Some(Box::new(add(
            Expr::Neg(P(Box::new(add(lit(1), lit(2))))),
            Expr::Sum(vec![lit(3), lit(4)]),
        ))),
    );

    let (v, s) = e.fold(&(), &Eval.pair(Show)); // tree still alive after
    println!("{s} = {v}");
    assert_eq!(v, 4);
    let v2 = e.fold(&(), &Eval); // fold again: it borrows
    assert_eq!(v2, 4);

    // non-Clone payload + Pair: previously a compile error, now fine
    let t = Tagged::Two(
        Box::new(Tagged::Tip(Opaque(3))),
        Box::new(Tagged::Two(
            Box::new(Tagged::Tip(Opaque(9))),
            Box::new(Tagged::Tip(Opaque(5))),
        )),
    );
    assert_eq!(t.fold(&(), &Count.pair(MaxTag)), (3, 9));
    println!("ok: zero clones, zero Comonoid, tree survives, custom pointer works");
}
