//! The documented numbers, re-earned on every `cargo test` — a stated
//! measurement that isn't re-verified is a future lie (we committed the
//! phantom-MSRV version of that sin once; this file is the penance).
use affine_cat::cata::{pair_owned, FoldAlg, IntoFoldAlg, Rebuild, Thunk};
use affine_cat_derive::Recursive;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static FORCED: AtomicUsize = AtomicUsize::new(0);

pub struct Live;
impl Drop for Live {
    fn drop(&mut self) {
        LIVE.fetch_sub(1, Relaxed);
    }
}
fn live() -> Live {
    let l = LIVE.fetch_add(1, Relaxed) + 1;
    PEAK.fetch_max(l, Relaxed);
    Live
}

#[derive(Recursive)]
enum Expr {
    Lit(Live, i64),
    Add(Live, Thunk<Expr>, Thunk<Expr>),
}
fn range(lo: i64, hi: i64) -> Expr {
    FORCED.fetch_add(1, Relaxed);
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
struct Find(i64);
impl FoldAlg<Expr, ()> for Find {
    type Out = Option<i64>;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, Self::Out>) -> Self::Out
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(_, n) if *n == self.0 => Some(*n),
            ExprLayer::Lit(_, _) => None,
            ExprLayer::Add(_, a, b) => a.or(b),
        }
    }
    fn absorbing(&self, o: &Self::Out) -> bool {
        o.is_some()
    }
}
struct FindOwned(i64);
impl IntoFoldAlg<Expr, ()> for FindOwned {
    type Out = Option<i64>;
    fn reduce(&self, _: &(), l: ExprLayerOwned<Self::Out>) -> Self::Out {
        match l {
            ExprLayerOwned::Lit(_, n) if n == self.0 => Some(n),
            ExprLayerOwned::Lit(_, _) => None,
            ExprLayerOwned::Add(_, a, b) => a.or(b),
        }
    }
    fn absorbing(&self, o: &Self::Out) -> bool {
        o.is_some()
    }
}

// single #[test]: the counters are process-global, so sequence the claims
#[test]
fn documented_numbers_still_hold() {
    // CLAIM (deforestation): 2^14-leaf virtual tree, peak liveness ~ path.
    const N: i64 = 1 << 14;
    let sum = range(1, N).into_fold(&(), &Sum);
    assert_eq!(sum, N * (N + 1) / 2);
    let peak = PEAK.load(Relaxed);
    assert!(peak <= 2 * 14 + 3, "peak {peak} exceeded path bound");
    assert_eq!(LIVE.load(Relaxed), 0);

    // CLAIM (fallible O(path)): search absorbs near the left edge.
    FORCED.store(0, Relaxed);
    let found = range(1, N).into_fold(&(), &FindOwned(1));
    assert_eq!(found, Some(1));
    let forced = FORCED.load(Relaxed);
    assert!(forced as i64 <= 2 * 14 + 2, "absorbed fold forced {forced}");

    // CLAIM (Rebuild x codata): identity forfeits annihilation — pairing
    // a search with Rebuild forces everything a lone search skips.
    fn spine(k: i64, cap: i64) -> Expr {
        FORCED.fetch_add(1, Relaxed);
        if k == cap {
            Expr::Lit(live(), -1)
        } else {
            Expr::Add(
                live(),
                Thunk::new(move || Expr::Lit(live(), k)),
                Thunk::new(move || spine(k + 1, cap)),
            )
        }
    }
    FORCED.store(0, Relaxed);
    assert_eq!(spine(0, 500).into_fold(&(), &FindOwned(3)), Some(3));
    let alone = FORCED.load(Relaxed);
    FORCED.store(0, Relaxed);
    let (_copy, f) = spine(0, 500).into_fold(&(), &pair_owned(Rebuild, Find(3)));
    assert_eq!(f, Some(3));
    let paired = FORCED.load(Relaxed);
    assert!(alone < 10, "lone search forced {alone}");
    assert!(paired >= 500, "paired-with-identity forced {paired} (all)");
}

// ===== #[recursive(scope)]: the AbsorbEnv theorems, live =====
mod scoped {
    use affine_cat::cata::{FoldAlg, ScopedEnv};
    use affine_cat_derive::Recursive;

    /// de Bruijn depth with saved-snapshot frames — the exact model of
    /// AbsorbEnv.agda (enter = suc, exit = restore saved).
    pub struct Depth(pub u32);
    impl ScopedEnv for Depth {
        type Frame = u32;
        fn enter(&mut self) -> u32 {
            let saved = self.0;
            self.0 += 1;
            saved
        }
        fn exit(&mut self, saved: u32) {
            self.0 = saved;
        }
    }

    #[derive(Recursive)]
    pub enum E {
        Var,
        Add(Box<E>, Box<E>),
        Lam(#[recursive(scope)] Box<E>),
    }

    /// leaves read the CURRENT depth from &Env — motion is driver-owned
    pub struct DepthAtVar;
    impl FoldAlg<E, Depth> for DepthAtVar {
        type Out = u32;
        fn reduce<'a>(&self, env: &Depth, l: ELayer<u32>) -> u32
        where
            E: 'a,
        {
            match l {
                ELayer::Var => env.0,
                ELayer::Add(a, b) => a.max(b),
                ELayer::Lam(b) => b,
            }
        }
    }

    /// absorbing algebra: Break escapes from UNDER binders
    pub struct FindDeep;
    impl FoldAlg<E, Depth> for FindDeep {
        type Out = Option<u32>;
        fn reduce<'a>(&self, env: &Depth, l: ELayer<Option<u32>>) -> Option<u32>
        where
            E: 'a,
        {
            match l {
                ELayer::Var if env.0 >= 2 => Some(env.0),
                ELayer::Var => None,
                ELayer::Add(a, b) => a.or(b),
                ELayer::Lam(b) => b,
            }
        }
        fn absorbing(&self, o: &Self::Out) -> bool {
            o.is_some()
        }
    }

    /// panicking algebra: unwinds from UNDER binders
    pub struct Bomb;
    impl FoldAlg<E, Depth> for Bomb {
        type Out = u32;
        fn reduce<'a>(&self, env: &Depth, l: ELayer<u32>) -> u32
        where
            E: 'a,
        {
            match l {
                ELayer::Var if env.0 >= 2 => panic!("boom at depth 2"),
                ELayer::Var => env.0,
                ELayer::Add(a, b) => a.max(b),
                ELayer::Lam(b) => b,
            }
        }
    }

    fn lam(e: E) -> E {
        E::Lam(Box::new(e))
    }

    #[test]
    fn scope_depth_break_and_panic_all_balanced() {
        // λ. λ. (var + var)  — leaves sit under two binders
        let t = lam(lam(E::Add(Box::new(E::Var), Box::new(E::Var))));

        // CLAIM (correctness): motion is driver-owned, term-driven.
        let mut env = Depth(0);
        assert_eq!(t.fold_in(&mut env, &DepthAtVar), 2);
        assert_eq!(env.0, 0, "balanced on the normal path");

        // CLAIM (balG, live): Break from under two binders restores both.
        let mut env = Depth(0);
        assert_eq!(t.fold_in(&mut env, &FindDeep), Some(2));
        assert_eq!(env.0, 0, "balanced on the absorption path (balG)");

        // CLAIM (Drop-guard panic leg): unwind restores both frames too.
        let mut env = Depth(0);
        let r =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| t.fold_in(&mut env, &Bomb)));
        assert!(r.is_err());
        assert_eq!(env.0, 0, "balanced even through a panic");
    }
}

// ===== derive robustness: named fields, generics, via-form =====
mod robust {
    use affine_cat::cata::{FoldAlg, IntoFoldAlg};
    use affine_cat_derive::Recursive;

    // named-field variants: patterns and layers in struct-variant syntax
    #[derive(Recursive)]
    enum Named {
        Leaf {
            tag: String,
        },
        Node {
            label: u32,
            left: Box<Named>,
            right: Box<Named>,
        },
    }
    struct Show;
    impl FoldAlg<Named, ()> for Show {
        type Out = String;
        fn reduce<'a>(&self, _: &(), l: NamedLayer<'a, String>) -> String
        where
            Named: 'a,
        {
            match l {
                NamedLayer::Leaf { tag } => tag.clone(),
                NamedLayer::Node { label, left, right } => {
                    format!("{label}({left},{right})")
                }
            }
        }
    }
    struct ShowOwned;
    impl IntoFoldAlg<Named, ()> for ShowOwned {
        type Out = String;
        fn reduce(&self, _: &(), l: NamedLayerOwned<String>) -> String {
            match l {
                NamedLayerOwned::Leaf { tag } => tag, // payload MOVED
                NamedLayerOwned::Node { label, left, right } => {
                    format!("{label}({left},{right})")
                }
            }
        }
    }

    // generic enum: type param propagates through layers and impls
    #[derive(Recursive)]
    enum GTree<P: Clone> {
        Tip(P),
        Fork(Box<GTree<P>>, Box<GTree<P>>),
    }
    struct CountG;
    impl<P: Clone> FoldAlg<GTree<P>, ()> for CountG {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: GTreeLayer<'a, P, usize>) -> usize
        where
            GTree<P>: 'a,
        {
            match l {
                GTreeLayer::Tip(_) => 1,
                GTreeLayer::Fork(a, b) => a + b,
            }
        }
    }

    // via-form: alias nested under a container, cured by the claimed type
    type BR = Box<Deep>;
    #[derive(Recursive)]
    enum Deep {
        End,
        Many(#[recursive(hole = "Vec<Box<Deep>>")] Vec<BR>),
    }
    struct CountD;
    impl FoldAlg<Deep, ()> for CountD {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: DeepLayer<usize>) -> usize
        where
            Deep: 'a,
        {
            match l {
                DeepLayer::End => 1,
                DeepLayer::Many(xs) => 1 + xs.iter().sum::<usize>(),
            }
        }
    }

    #[test]
    fn named_generic_and_via_all_fold() {
        let t = Named::Node {
            label: 7,
            left: Box::new(Named::Leaf { tag: "a".into() }),
            right: Box::new(Named::Leaf { tag: "b".into() }),
        };
        assert_eq!(t.fold(&(), &Show), "7(a,b)");
        assert_eq!(t.into_fold(&(), &ShowOwned), "7(a,b)");

        let g = GTree::Fork(
            Box::new(GTree::Tip("x")),
            Box::new(GTree::Fork(
                Box::new(GTree::Tip("y")),
                Box::new(GTree::Tip("z")),
            )),
        );
        assert_eq!(g.fold(&(), &CountG), 3);

        let d = Deep::Many(vec![
            Box::new(Deep::End),
            Box::new(Deep::Many(vec![Box::new(Deep::End)])),
        ]);
        assert_eq!(d.fold(&(), &CountD), 4, "alias under Vec: every node seen");
    }
}

// ===== try_fold2: the non-scoped family drivers, first coverage =====
mod family_plain {
    use affine_cat_derive::recursive_family;

    #[recursive_family]
    mod ast {
        pub enum Expr {
            Num(i64),
            Sum(Box<Expr>, Box<Expr>),
            First(Box<Stmt>),
        }
        pub enum Stmt {
            Skip,
            Eval(Box<Expr>),
            Seq(Vec<Stmt>),
        }
    }
    use ast::*;

    /// evaluate; division-by-zero-style poison absorbs at the EXPR sort
    struct Eval;
    impl ExprStmtFold<()> for Eval {
        type Out1 = Option<i64>;
        type Out2 = Option<i64>;
        fn reduce_expr<'a>(&self, _: &(), l: ExprLayer<Self::Out1, Self::Out2>) -> Self::Out1 {
            match l {
                ExprLayer::Num(n) => Some(*n),
                ExprLayer::Sum(a, b) => a?.checked_add(b?), // overflow: Expr-born None
                ExprLayer::First(s) => s,
            }
        }
        fn reduce_stmt<'a>(&self, _: &(), l: StmtLayer<Self::Out1, Self::Out2>) -> Self::Out2 {
            match l {
                StmtLayer::Skip => Some(0),
                StmtLayer::Eval(e) => e,
                // sum of statement values — ANNIHILATES on any absorbed
                // child, as the law requires. (A `last()` version was
                // tried first: it discards absorbed non-last children,
                // violates annihilation, and fold2/try_fold2 observably
                // disagree — the law's necessity, observed live.)
                StmtLayer::Seq(xs) => {
                    if xs.is_empty() {
                        return None; // empty: Stmt-born poison
                    }
                    xs.into_iter().try_fold(0i64, |acc, x| Some(acc + x?))
                }
            }
        }
    }
    impl ExprStmtAbsorb<()> for Eval {
        fn absorbing1(&self, o: &Self::Out1) -> bool {
            o.is_none()
        }
        fn absorbing2(&self, o: &Self::Out2) -> bool {
            o.is_none()
        }
        // identical Outs: promotes are identities — the bubble-form laws
        // hold with plain annihilation (TwoAbsorb's easy case), and the
        // license is env-independent (ScopedAbsorb's demand, trivially)
        fn promote_2_to_1(&self, o: Self::Out2) -> Self::Out1 {
            o
        }
        fn promote_1_to_2(&self, o: Self::Out1) -> Self::Out2 {
            o
        }
    }

    /// Stmt-born poison: the empty Seq
    fn stmt_poison() -> Expr {
        Expr::First(Box::new(Stmt::Seq(vec![])))
    }
    /// Expr-born poison: overflow
    fn expr_poison() -> Expr {
        Expr::Sum(Box::new(Expr::Num(i64::MAX)), Box::new(Expr::Num(1)))
    }

    #[test]
    fn try_fold2_both_entries_and_both_bubbles() {
        // plain agreement on the happy path (T-X's continue branch)
        let e = Expr::Sum(Box::new(Expr::Num(2)), Box::new(Expr::Num(3)));
        assert_eq!(e.fold2(&(), &Eval), Some(5));
        assert_eq!(e.try_fold2(&(), &Eval), Some(5));

        // Stmt-born (b2) bubble exits at an Expr entry: promote_2_to_1 runs
        let cross = Expr::Sum(
            Box::new(Expr::Num(1)),
            Box::new(Expr::First(Box::new(Stmt::Seq(vec![
                Stmt::Skip,
                Stmt::Eval(Box::new(stmt_poison())),
            ])))),
        );
        assert_eq!(cross.try_fold2(&(), &Eval), None);

        // Expr-born (b1) bubble exits at a Stmt entry: promote_1_to_2 runs
        let s = Stmt::Seq(vec![Stmt::Eval(Box::new(expr_poison())), Stmt::Skip]);
        assert_eq!(s.try_fold2(&(), &Eval), None);
        // and agreement with the plain driver on the same tree (T-X live)
        assert_eq!(s.fold2(&(), &Eval), s.try_fold2(&(), &Eval));
    }
}

// ===== zero-coverage sweep: shipped paths never executed =====
mod coverage_sweep {
    use affine_cat::cata::{IntoFoldAlg, ScopedEnv, ScopedEnvWith, Thunk};
    use affine_cat_derive::{recursive_family, Recursive};

    // (1) codata under the consuming derive (Thunk's first test-side
    // witness; previously example-only). ThunkSend was cut — the dfa
    // standard — and this test carried its coverage over.
    #[derive(Recursive)]
    enum Lazy {
        Now(i64),
        Later(Thunk<Box<Lazy>>),
        Both(Box<Lazy>, Thunk<Box<Lazy>>),
    }
    struct Force;
    impl IntoFoldAlg<Lazy, ()> for Force {
        type Out = i64;
        fn reduce(&self, _: &(), l: LazyLayerOwned<i64>) -> i64 {
            match l {
                LazyLayerOwned::Now(n) => n,
                LazyLayerOwned::Later(x) => x,
                LazyLayerOwned::Both(a, b) => a + b,
            }
        }
    }

    // (2) generic enum × consuming: RecursiveOwned<GTree<P>> compiled in
    // the robustness witness but was never CALLED — the owned_where
    // 'static path runs here. (3) via-form × consuming, same gap.
    #[derive(Recursive)]
    enum GT<P: Clone> {
        Tip(P),
        Fork(Box<GT<P>>, Box<GT<P>>),
    }
    struct JoinG;
    // 'static: the consuming machinery's bounded-HRTB wall, surfacing
    // at the consumer exactly as the RecursiveOwned impl documents
    impl<P: Clone + Into<String> + 'static> IntoFoldAlg<GT<P>, ()> for JoinG {
        type Out = String;
        fn reduce(&self, _: &(), l: GTLayerOwned<P, String>) -> String {
            match l {
                GTLayerOwned::Tip(p) => p.into(),
                GTLayerOwned::Fork(a, b) => format!("({a}{b})"),
            }
        }
    }
    type BD = Box<Deep2>;
    #[derive(Recursive)]
    enum Deep2 {
        End,
        Many(#[recursive(hole = "Vec<Box<Deep2>>")] Vec<BD>),
    }
    struct CountD2;
    impl IntoFoldAlg<Deep2, ()> for CountD2 {
        type Out = usize;
        fn reduce(&self, _: &(), l: Deep2LayerOwned<usize>) -> usize {
            match l {
                Deep2LayerOwned::End => 1,
                Deep2LayerOwned::Many(xs) => 1 + xs.iter().sum::<usize>(),
            }
        }
    }

    // (4) scoped try at the SECOND-sort entry + (5) scope_prev whose
    // prev is Vec-wrapped (the mapped-chain ScopedEnvWith bound,
    // never generated before)
    #[recursive_family]
    mod q {
        pub enum Cond {
            #[allow(dead_code)]
            T,
            Ref(usize),
        }
        pub enum Blk {
            Leaf(i64),
            // Vec-wrapped prev feeds the scoped hole's frame
            Group(Vec<Blk>, #[recursive(scope_prev)] Box<Cond>),
        }
    }
    use q::*;

    struct Depths {
        stack: Vec<usize>, // frame: group sizes visible
    }
    impl ScopedEnv for Depths {
        type Frame = usize;
        fn enter(&mut self) -> usize {
            self.stack.len()
        }
        fn exit(&mut self, saved: usize) {
            self.stack.truncate(saved);
        }
    }
    impl ScopedEnvWith<Vec<Option<i64>>> for Depths {
        fn enter_with(&mut self, kids: &Vec<Option<i64>>) -> usize {
            let saved = self.stack.len();
            self.stack.push(kids.len());
            saved
        }
    }
    struct Check;
    impl CondBlkFold<Depths> for Check {
        type Out1 = Option<i64>; // None = ill-formed condition
        type Out2 = Option<i64>;
        fn reduce_cond<'a>(
            &self,
            env: &Depths,
            l: CondLayer, // hole-less sort: params pruned (E0392 fix)
        ) -> Self::Out1 {
            match l {
                CondLayer::T => Some(1),
                CondLayer::Ref(i) => {
                    // resolves against the SIBLING GROUP's size — the
                    // Vec-prev frame content, live
                    let n = *env.stack.last()?;
                    if *i < n {
                        Some(*i as i64)
                    } else {
                        None
                    }
                }
            }
        }
        fn reduce_blk<'a>(&self, _: &Depths, l: BlkLayer<Self::Out1, Self::Out2>) -> Self::Out2 {
            match l {
                BlkLayer::Leaf(n) => Some(*n),
                BlkLayer::Group(kids, cond) => {
                    Some(kids.into_iter().flatten().sum::<i64>() + cond?)
                }
            }
        }
    }
    impl CondBlkAbsorb<Depths> for Check {
        fn absorbing1(&self, o: &Self::Out1) -> bool {
            o.is_none()
        }
        fn promote_2_to_1(&self, o: Self::Out2) -> Self::Out1 {
            o
        }
        fn promote_1_to_2(&self, o: Self::Out1) -> Self::Out2 {
            o
        }
    }

    #[test]
    fn sweep() {
        // (1) Thunk forces lazily under consuming fold
        let l = Lazy::Both(
            Box::new(Lazy::Now(2)),
            Thunk::new(|| Box::new(Lazy::Later(Thunk::new(|| Box::new(Lazy::Now(40)))))),
        );
        assert_eq!(l.into_fold(&(), &Force), 42);

        // (2) generic consuming: the 'static owned path runs
        let g: GT<&'static str> = GT::Fork(Box::new(GT::Tip("a")), Box::new(GT::Tip("b")));
        assert_eq!(g.into_fold(&(), &JoinG), "(ab)");

        // (3) via-form consuming
        let d = Deep2::Many(vec![Box::new(Deep2::End), Box::new(Deep2::End)]);
        assert_eq!(d.into_fold(&(), &CountD2), 3);

        // (4)+(5): Vec-prev frame feeds resolution; Blk entry = the
        // SECOND-sort scoped try driver, previously never called
        let ok = Blk::Group(
            vec![Blk::Leaf(10), Blk::Leaf(20)],
            Box::new(Cond::Ref(1)), // 1 < 2: resolves
        );
        let mut env = Depths { stack: vec![] };
        assert_eq!(ok.try_fold_in2(&mut env, &Check), Some(31));
        assert!(env.stack.is_empty(), "balanced");

        // a Cond-born (b1) bubble exiting at the Blk entry:
        // promote_1_to_2 in the SCOPED configuration, first execution
        let bad = Blk::Group(vec![Blk::Leaf(1)], Box::new(Cond::Ref(5)));
        let mut env = Depths { stack: vec![] };
        assert_eq!(bad.try_fold_in2(&mut env, &Check), None);
        assert!(env.stack.is_empty(), "balanced through the scoped bubble");
    }
}

// ===== §2 (sqlfront report): forced holes get the borrowed face ONLY =====
mod forced_hole_gate {
    use affine_cat::cata::{FoldAlg, Hole, Holes};
    use affine_cat_derive::Recursive;
    use core::ops::ControlFlow;
    use std::rc::Rc;

    /// a shared handle: pointer-shaped for the borrowed face, and — being
    /// shared — legitimately WITHOUT `HolesMove`. Before the gate fix the
    /// derive demanded it anyway (E0277); this module compiling IS the fix.
    #[derive(Clone)]
    struct H(Rc<N>);

    #[derive(Recursive)]
    enum N {
        Leaf(i64),
        Chain(#[recursive(hole)] H),
    }

    impl Hole<N> for H {
        type Mapped<U> = U;
        fn unzip_with<P, A, B>(m: P, split: &mut dyn FnMut(P) -> (A, B)) -> (A, B) {
            split(m)
        }
    }
    impl Holes<N> for H {
        fn map_ref<U>(&self, f: &mut dyn FnMut(&N) -> U) -> U {
            f(&self.0)
        }
        fn try_map_ref<U>(&self, f: &mut dyn FnMut(&N) -> ControlFlow<U, U>) -> ControlFlow<U, U> {
            f(&self.0)
        }
        fn map_ref_until<B, U>(
            &self,
            f: &mut dyn FnMut(&N) -> ControlFlow<B, U>,
        ) -> ControlFlow<B, U> {
            f(&self.0)
        }
    }
    // deliberately NO HolesMove, NO HolesWrap

    struct Sum;
    impl FoldAlg<N, ()> for Sum {
        type Out = i64;
        fn reduce<'a>(&self, _: &(), l: NLayer<'a, i64>) -> i64
        where
            N: 'a,
        {
            match l {
                NLayer::Leaf(n) => *n,
                NLayer::Chain(x) => x + 1,
            }
        }
    }

    #[test]
    fn borrowed_face_without_consuming_machinery() {
        let t = N::Chain(H(Rc::new(N::Chain(H(Rc::new(N::Leaf(40)))))));
        assert_eq!(t.fold(&(), &Sum), 42);
    }
}

// ===== §3 (sqlfront report): Vec IS a scope stack, no newtype =====
mod blanket_scoped_env {
    use affine_cat::cata::FoldAlg;
    use affine_cat_derive::Recursive;

    #[derive(Recursive)]
    enum B {
        Leaf,
        Bind(#[recursive(scope)] Box<B>),
    }
    struct Depth;
    impl FoldAlg<B, Vec<u32>> for Depth {
        type Out = usize;
        fn reduce<'a>(&self, env: &Vec<u32>, l: BLayer<usize>) -> usize
        where
            B: 'a,
        {
            match l {
                BLayer::Leaf => env.len(), // the frame count, read raw
                BLayer::Bind(d) => d,
            }
        }
    }

    #[test]
    fn vec_is_the_env() {
        let t = B::Bind(Box::new(B::Bind(Box::new(B::Leaf))));
        let mut env: Vec<u32> = vec![];
        // enter pushes nothing (snapshot frames) — depth reads 0 here;
        // the point is the TYPE: Vec<u32> drives fold_in directly
        assert_eq!(t.fold_in(&mut env, &Depth), 0);
        assert!(env.is_empty(), "balanced");
    }
}

// ===== composition-gap witnesses =====
mod composition_blankets {
    use affine_cat::cata::{pair, FoldAlg};
    use affine_cat_derive::Recursive;
    use std::rc::Rc;

    // shared pointers auto-classify as borrowed-face holes: plain field,
    // no attribute, in-crate Rc impls, movable gate excludes consuming
    #[derive(Recursive)]
    enum S {
        Leaf(i64),
        Shared(Rc<S>),
    }
    struct Count;
    impl FoldAlg<S, ()> for Count {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: SLayer<'a, usize>) -> usize
        where
            S: 'a,
        {
            match l {
                SLayer::Leaf(_) => 1,
                SLayer::Shared(n) => n + 1,
            }
        }
    }
    struct Depth;
    impl FoldAlg<S, ()> for Depth {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: SLayer<'a, usize>) -> usize
        where
            S: 'a,
        {
            match l {
                SLayer::Leaf(_) => 0,
                SLayer::Shared(d) => d + 1,
            }
        }
    }

    #[test]
    fn rc_is_a_borrowed_hole_and_algebras_pair_by_reference() {
        let t = S::Shared(Rc::new(S::Shared(Rc::new(S::Leaf(7)))));
        let (c, d) = t.fold(&(), &pair(&Count, &Depth)); // borrowed algebras
        assert_eq!((c, d), (3, 2));
        let c2 = t.fold(&(), &Count); // originals still owned — reused
        assert_eq!(c2, 3);
    }
}

// ===== [persona delta] ByRef closes Driven(&mut transducer) =====
mod by_ref_transducer {
    use affine_cat::base::Absorb;
    use affine_cat::machines::{from_fn, ByRef, Driven};

    #[test]
    fn driven_by_ref_composes_and_returns_the_transducer() {
        let mut t = from_fn(|x: u64| x * 2);
        {
            let mut sink = Driven(ByRef(&mut t));
            sink.absorb(1);
            sink.absorb(2);
        } // borrow ends; t is still ours — the Iterator::by_ref shape
        let mut again = Driven(ByRef(&mut t));
        again.absorb(3);
    }
}

// ===== [persona delta] custom pointer, plain field, no attribute =====
mod custom_pointer_no_attr {
    use affine_cat::cata::{FoldAlg, Hole, Holes};
    use affine_cat_derive::Recursive;
    use core::ops::ControlFlow;

    struct P<T>(Box<T>);
    impl<T> Hole<T> for P<T> {
        type Mapped<U> = U;
        fn unzip_with<Pp, A, B>(m: Pp, split: &mut dyn FnMut(Pp) -> (A, B)) -> (A, B) {
            split(m)
        }
    }
    impl<T> Holes<T> for P<T> {
        fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> U {
            f(&self.0)
        }
        fn try_map_ref<U>(&self, f: &mut dyn FnMut(&T) -> ControlFlow<U, U>) -> ControlFlow<U, U> {
            f(&self.0)
        }
        fn map_ref_until<B, U>(
            &self,
            f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
        ) -> ControlFlow<B, U> {
            f(&self.0)
        }
    }

    #[derive(Recursive)]
    enum T2 {
        Leaf(i64),
        Own(P<T2>), // plain field: the classifier chains ANY wrapper
    }
    struct Count;
    impl FoldAlg<T2, ()> for Count {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: T2Layer<'a, usize>) -> usize
        where
            T2: 'a,
        {
            match l {
                T2Layer::Leaf(_) => 1,
                T2Layer::Own(n) => n + 1,
            }
        }
    }
    #[test]
    fn doc_claim_is_a_test_not_a_comment() {
        let t = T2::Own(P(Box::new(T2::Leaf(1))));
        assert_eq!(t.fold(&(), &Count), 2);
    }
}
