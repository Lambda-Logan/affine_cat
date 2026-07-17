//! Deforested hylomorphism, consuming-only edition: `Thunk` grants no
//! borrowed forcing (the husk sacrifice), so codata folds go through
//! `into_fold` — where a second fold is E0382, and single-forcing is
//! enforced by the checker. Two passes fuse via `PairOwned`.
use affine_cat::cata::{FoldAlg, IntoFoldAlg, PairOwned, Thunk};
use affine_cat_derive::Recursive;
use std::cell::LazyCell;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static TOTAL: AtomicUsize = AtomicUsize::new(0);
fn born() {
    let l = LIVE.fetch_add(1, Relaxed) + 1;
    PEAK.fetch_max(l, Relaxed);
    TOTAL.fetch_add(1, Relaxed);
}

/// per-node liveness token (payload, so Expr stays Drop-free for into_fold)
pub struct Live;
impl Drop for Live {
    fn drop(&mut self) {
        LIVE.fetch_sub(1, Relaxed);
    }
}
fn live() -> Live {
    born();
    Live
}

#[derive(Recursive)]
enum Expr {
    Lit(Live, i64),
    Add(Live, Thunk<Expr>, Thunk<Expr>),
}

fn range(lo: i64, hi: i64) -> Expr {
    if lo == hi {
        Expr::Lit(live(), lo)
    } else {
        let mid = lo + (hi - lo) / 2;
        Expr::Add(
            live(),
            Thunk::new(move || range(lo, mid)),
            Thunk::new(move || range(mid + 1, hi)),
        )
    }
}

struct Sum;
impl IntoFoldAlg<Expr, ()> for Sum {
    type Out = i64;
    fn reduce(&self, _: &(), l: ExprLayerOwned<i64>) -> i64 {
        match l {
            ExprLayerOwned::Lit(_, n) => n,
            ExprLayerOwned::Add(_, a, b) => a + b,
        }
    }
}
/// borrowed analysis riding a consuming pass: PairOwned lends it the layer
struct Depth;
impl FoldAlg<Expr, ()> for Depth {
    type Out = u32;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, u32>) -> u32
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(_, _) => 0,
            ExprLayer::Add(_, a, b) => 1 + a.max(b),
        }
    }
}

fn main() {
    const N: i64 = 1 << 17; // 131072 leaves -> 262143 nodes if materialized

    // Codata is affine, now statically: the fusion of two passes is
    // PairOwned, and there is no second fold to mistakenly write.
    let (sum, depth) = range(1, N).into_fold(&(), &PairOwned(Sum, Depth));
    assert_eq!(sum, N * (N + 1) / 2);
    assert_eq!(depth, 17);
    let (total, peak, live_now) = (TOTAL.load(Relaxed), PEAK.load(Relaxed), LIVE.load(Relaxed));
    println!("nodes produced: {total}, peak live: {peak}, live now: {live_now}");
    assert_eq!(total as i64, 2 * N - 1, "the whole tree was produced...");
    assert!(peak <= 2 * 17 + 3, "...but never existed: peak ~ path");
    assert_eq!(live_now, 0);

    // Call-by-NEED contrast: LazyCell holes defer but RETAIN — no thunks,
    // so this IR keeps the borrowed fold and refolds freely.
    #[derive(Recursive)]
    enum L {
        Tip(i64),
        Node(LazyCell<Box<L>>, LazyCell<Box<L>>),
    }
    struct SumL;
    impl FoldAlg<L, ()> for SumL {
        type Out = i64;
        fn reduce<'a>(&self, _: &(), l: LLayer<'a, i64>) -> i64
        where
            L: 'a,
        {
            match l {
                LLayer::Tip(n) => *n,
                LLayer::Node(a, b) => a + b,
            }
        }
    }
    let t = L::Node(
        LazyCell::new(|| Box::new(L::Tip(2))),
        LazyCell::new(|| {
            Box::new(L::Node(LazyCell::new(|| Box::new(L::Tip(3))), LazyCell::new(|| Box::new(L::Tip(4)))))
        }),
    );
    assert_eq!(t.fold(&(), &SumL), 9);
    assert_eq!(t.fold(&(), &SumL), 9); // memoized: refolding is fine HERE

    // FALLIBLE OVER CODATA: absorbing Err on the consuming path.
    static FORCED: AtomicUsize = AtomicUsize::new(0);
    fn poisoned(lo: i64, hi: i64, bad: i64) -> Expr {
        FORCED.fetch_add(1, Relaxed);
        if lo == hi {
            Expr::Lit(live(), if lo == bad { i64::MIN } else { lo })
        } else {
            let mid = lo + (hi - lo) / 2;
            Expr::Add(
                live(),
                Thunk::new(move || poisoned(lo, mid, bad)),
                Thunk::new(move || poisoned(mid + 1, hi, bad)),
            )
        }
    }
    struct TrySum;
    impl IntoFoldAlg<Expr, ()> for TrySum {
        type Out = Result<i64, String>;
        fn reduce(&self, _: &(), l: ExprLayerOwned<Self::Out>) -> Self::Out {
            match l {
                ExprLayerOwned::Lit(_, n) if n == i64::MIN => Err("poisoned leaf".into()),
                ExprLayerOwned::Lit(_, n) => Ok(n),
                ExprLayerOwned::Add(_, a, b) => Ok(a? + b?),
            }
        }
        fn absorbing(&self, out: &Self::Out) -> bool {
            out.is_err()
        }
    }
    let r = poisoned(1, N, 3).into_fold(&(), &TrySum);
    assert!(r.is_err());
    let forced = FORCED.load(Relaxed);
    println!("fallible over codata: err after forcing {forced} of {} nodes", 2 * N - 1);
    assert!(forced as i64 <= 2 * 17 + 2, "error forced a path, not the tree");

    // SEARCH OVER AN INFINITE TREE, consuming path. Order caveat stands:
    // finite work declared before the infinite tail, or the fold diverges.
    static SEARCHED: AtomicUsize = AtomicUsize::new(0);
    fn naturals(k: i64) -> Expr {
        SEARCHED.fetch_add(1, Relaxed);
        Expr::Add(
            live(),
            Thunk::new(move || Expr::Lit(live(), k)),
            Thunk::new(move || naturals(k + 1)),
        )
    }
    struct Find(i64);
    impl IntoFoldAlg<Expr, ()> for Find {
        type Out = Option<i64>;
        fn reduce(&self, _: &(), l: ExprLayerOwned<Self::Out>) -> Self::Out {
            match l {
                ExprLayerOwned::Lit(_, n) if n == self.0 => Some(n),
                ExprLayerOwned::Lit(_, _) => None,
                ExprLayerOwned::Add(_, a, b) => a.or(b),
            }
        }
        fn absorbing(&self, out: &Self::Out) -> bool {
            out.is_some()
        }
    }
    let found = naturals(0).into_fold(&(), &Find(40));
    assert_eq!(found, Some(40));
    let searched = SEARCHED.load(Relaxed);
    println!("infinite-tree search: found 40 after {searched} spine nodes");
    assert!(searched <= 42, "terminated by annihilation, not by data");

    println!("deforested hylo: ok  |  call-by-need: ok  |  fallible: ok  |  infinite search: ok");
}
