//! The four unfixable walls, each demonstrated firing, with the lawful
//! alternative beside it. Compile-error walls are probed separately.
use affine_cat::cata::{run, FoldAlg, IntoFoldAlg, PairOwned, Rebuild, Recursor, Thunk};
use affine_cat_derive::Recursive;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static FORCED: AtomicUsize = AtomicUsize::new(0);

#[derive(Recursive)]
enum Expr {
    Lit(i64),
    Add(Thunk<Expr>, Thunk<Expr>),
}
fn th(f: impl FnOnce() -> Expr + 'static) -> Thunk<Expr> {
    Thunk::new(move || {
        FORCED.fetch_add(1, Relaxed);
        f()
    })
}
struct SumOwned;
impl IntoFoldAlg<Expr, ()> for SumOwned {
    type Out = i64;
    fn reduce(&self, _: &(), l: ExprLayerOwned<i64>) -> i64 {
        match l {
            ExprLayerOwned::Lit(n) => n,
            ExprLayerOwned::Add(a, b) => a + b,
        }
    }
}
struct Find(i64);
// borrowed algebras remain legal for codata IRs — the Layer type exists;
// only the standalone borrowed DRIVER is gone. They ride inside PairOwned.
impl FoldAlg<Expr, ()> for Find {
    type Out = Option<i64>;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, Self::Out>) -> Self::Out
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(n) if *n == self.0 => Some(*n),
            ExprLayer::Lit(_) => None,
            ExprLayer::Add(a, b) => a.or(b),
        }
    }
    fn absorbing(&self, o: &Self::Out) -> bool {
        o.is_some()
    }
}
impl IntoFoldAlg<Expr, ()> for Find {
    type Out = Option<i64>;
    fn reduce(&self, _: &(), l: ExprLayerOwned<Self::Out>) -> Self::Out {
        match l {
            ExprLayerOwned::Lit(n) if n == self.0 => Some(n),
            ExprLayerOwned::Lit(_) => None,
            ExprLayerOwned::Add(a, b) => a.or(b),
        }
    }
    fn absorbing(&self, o: &Self::Out) -> bool {
        o.is_some()
    }
}

fn tree() -> Expr {
    Expr::Add(
        th(|| Expr::Lit(1)),
        th(|| Expr::Add(th(|| Expr::Lit(2)), th(|| Expr::Lit(3)))),
    )
}
fn spine(k: i64, cap: i64) -> Expr {
    if k == cap {
        Expr::Lit(-1)
    } else {
        Expr::Add(th(move || Expr::Lit(k)), th(move || spine(k + 1, cap)))
    }
}

// ---- WALL 3 support: a knot-tying ring, no derive, folded via Recursor ----
struct Ring {
    next: RefCell<Option<Rc<Ring>>>,
}
struct Hops;
impl Recursor<Ring, u32> for Hops {
    type Out = u32;
    fn step(
        &self,
        fuel: &mut u32,
        node: &Ring,
        rec: &mut dyn FnMut(&mut u32, &Ring) -> u32,
    ) -> u32 {
        if *fuel == 0 {
            return 0; // descent-side fuel: the ONLY thing that stops a cycle
        }
        *fuel -= 1;
        match &*node.next.borrow() {
            Some(n) => 1 + rec(fuel, n),
            None => 0,
        }
    }
}

#[allow(deprecated)] // the positivity-lint demo fires inside
fn main() {
    // ============ WALL 1: the husk (semantic) — DEMOLISHED ============
    // Formerly: borrowed fold over Thunk holes returned through `&self`
    // and left a husk that panicked on refold (this section used to
    // demonstrate the panic under catch_unwind). The wall was removed by
    // sacrifice: Thunk no longer implements `Holes`, so the borrowed fold
    // over a codata IR IS NOT GENERATED — `tree().fold(...)` does not
    // compile. The consuming path remains, where the husk is E0382:
    assert_eq!(tree().into_fold(&(), &SumOwned), 6);
    // t.into_fold(...); t.into_fold(...)  // <- use of moved value (probe)
    println!("wall 1 (husk): demolished — refold went from runtime panic to unwritable");

    // ============ WALL 3: cycles + positivity (information) ============
    let a = Rc::new(Ring {
        next: RefCell::new(None),
    });
    let b = Rc::new(Ring {
        next: RefCell::new(Some(a.clone())),
    });
    *a.next.borrow_mut() = Some(b.clone()); // the knot: safe Rust, no warning
    let mut fuel = 10_000;
    let hops = run(&Hops, &mut fuel, &a);
    assert_eq!(hops, 10_000, "a 2-node cycle absorbs any budget");
    // note: cata-style absorption could NOT have stopped this — absorption
    // fires on child RESULTS, and a cycle has no leaves, so no reduce ever
    // runs. Only descent-side control (the Recursor face) can bail.
    println!("wall 3 (cycle): 2 nodes, {hops} hops, stopped by fuel, not by data");

    // positivity: nothing stops the non-positive occurrence from deriving
    // the token-level positivity LINT fires here (deprecated-shim with
    // user-code spans) — allowed because firing is the point of the demo
    #[allow(deprecated)]
    #[derive(Recursive)]
    #[allow(dead_code)]
    enum Bad {
        Fun(Box<dyn Fn(Bad) -> Bad>), // Bad in negative position: compiles fine
        Two(Box<Bad>, Box<Bad>),
    }
    println!("wall 3 (positivity): non-positive Layer derived without complaint");

    // ============ WALL 4: Rebuild x codata (theorem wall) ============
    FORCED.store(0, Relaxed);
    let copy = tree().into_fold(&(), &Rebuild);
    let forced_by_identity = FORCED.load(Relaxed);
    assert_eq!(forced_by_identity, 4, "the IDENTITY forced every thunk");
    assert_eq!(copy.into_fold(&(), &SumOwned), 6); // equal tree, laziness destroyed
                                                   // and pairing Rebuild with a search forfeits termination-by-annihilation:
    FORCED.store(0, Relaxed);
    assert_eq!(spine(0, 2_000).into_fold(&(), &Find(3)), Some(3));
    let search_alone = FORCED.load(Relaxed);
    FORCED.store(0, Relaxed);
    let (_copy, found) = spine(0, 2_000).into_fold(&(), &PairOwned(Rebuild, Find(3)));
    assert_eq!(found, Some(3));
    let paired = FORCED.load(Relaxed);
    println!(
        "wall 4 (Rebuild x codata): search alone forced {search_alone}, \
         paired with the identity forced {paired} (all of them) — over an \
         infinite tree that difference is divergence"
    );
    assert!(search_alone < 10 && paired >= 4_000);

    // ============ CEILING: token-level typing (silent alias) ============
    type BExpr = Box<Aliased>; // classifier cannot see through this
    #[derive(Recursive)]
    enum Aliased {
        Leaf,
        Good(Box<Aliased>),
        Sneaky(BExpr), // silently a PAYLOAD: the child below it is invisible
    }
    struct Count;
    impl FoldAlg<Aliased, ()> for Count {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: AliasedLayer<'a, usize>) -> usize
        where
            Aliased: 'a,
        {
            match l {
                AliasedLayer::Leaf => 1,
                AliasedLayer::Good(n) => 1 + n,
                AliasedLayer::Sneaky(_) => 1, // the &BExpr payload hides a node
            }
        }
    }
    let t = Aliased::Good(Box::new(Aliased::Sneaky(Box::new(Aliased::Leaf))));
    let n = t.fold(&(), &Count);
    assert_eq!(n, 2, "three nodes, counted as two: SILENTLY wrong");

    // — and the relief valve, now shipped: #[recursive(hole)] hands the
    // alias to rustc, which sees through it where tokens cannot.
    #[derive(Recursive)]
    enum Cured {
        Leaf,
        Good(Box<Cured>),
        Sneaky(#[recursive(hole)] BCured),
    }
    type BCured = Box<Cured>;
    struct CountC;
    impl FoldAlg<Cured, ()> for CountC {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: CuredLayer<usize>) -> usize
        where
            Cured: 'a,
        {
            match l {
                CuredLayer::Leaf => 1,
                CuredLayer::Good(n) => 1 + n,
                CuredLayer::Sneaky(n) => 1 + n, // now a real hole: T, not &BCured
            }
        }
    }
    let t = Cured::Good(Box::new(Cured::Sneaky(Box::new(Cured::Leaf))));
    assert_eq!(t.fold(&(), &CountC), 3, "escape hatch: counted correctly");

    // the dual hatch: #[recursive(payload)] demotes a would-be hole —
    // a QUOTED subtree is data, not structure; the fold must not descend.
    #[derive(Recursive)]
    enum Q {
        Leaf,
        Node(Box<Q>),
        Quote(#[recursive(payload)] Box<Q>),
    }
    struct CountQ;
    impl FoldAlg<Q, ()> for CountQ {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: QLayer<'a, usize>) -> usize
        where
            Q: 'a,
        {
            match l {
                QLayer::Leaf => 1,
                QLayer::Node(n) => 1 + n,
                QLayer::Quote(_) => 1, // &Box<Q>: opaque by declaration
            }
        }
    }
    let q = Q::Node(Box::new(Q::Quote(Box::new(Q::Leaf))));
    assert_eq!(q.fold(&(), &CountQ), 2, "quoted subtree correctly opaque");

    println!("ceiling (alias): silent miscount still demonstrable; both escape hatches cure it");
}
