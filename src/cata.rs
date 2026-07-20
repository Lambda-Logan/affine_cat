//! Recursion schemes over owned trees with an ambient environment: the
//! promoted `cata` item from the Deferred list, corrected.
//!
//! The deferral sketched `fold_with(alg: impl Piece<Layer<B>, Out = B>)`.
//! That shape is wrong in a way a downstream compiler back-end exposed: a
//! catamorphism's algebra is bottom-up, so by the time it receives
//! `Layer<B>` the children are folded — no algebra of that type can modify
//! the environment *on descent into a binder*, which is exactly what
//! binder-crossing passes (resolve, typecheck, evaluate) need. The escape
//! is carrier enrichment (fold into `Env -> B`), i.e. the exponential this
//! crate refuses to port; what ships instead is its defunctionalization,
//! in two faces:
//!
//! * [`Recursor`] / [`Recursor2`] — the general face: the algebra receives
//!   the *unfolded* node plus recurse-continuations, environment and
//!   borrowed node handed together. This is [`crate::cps::Piece`]'s
//!   continuation idiom pointed down the tree instead of along the
//!   pipeline. Object-safe, **no GATs** — the "GAT costs `dyn`" line the
//!   deferral priced does not apply to this face at all.
//! * The *bracketed* pattern (per-IR code; see the module example) — the
//!   lawful view: a per-(IR, Env) scope discipline (descend/ascend with a
//!   moved frame, so unbalanced scopes are unrepresentable) wrapped around
//!   a bottom-up [`FoldAlg`]. Edge identity lives where it is visible for
//!   free — per-IR code matching its own constructors — so no edge-tag API
//!   is needed, and the generic face stays this small.
//!
//! [`FoldAlg`] is the bottom-up algebra over a [`Recursive`] pattern
//! functor, and [`Pair`] is banana-split: two algebras, one traversal.
//! `Pair` needs [`Recursive::unzip`], whose payload duplication is gated
//! on [`crate::base::Comonoid`] by the implementor — the explicit bound
//! where CCC-ported banana-split hides a silent `Clone`.
//!
//! **Traversal order is contract, not accident**: children fold in
//! declaration order. Pure algebras cannot observe it; it IS observable
//! through absorption priority (first absorbing value in order wins),
//! future scope motion (a binder's siblings must be declared in scoping
//! order), and codata forcing (finite work must be declared before an
//! infinite tail, or the fold diverges). Field order is semantics.
//!
//! # For recursion-schemes users (the Kmett dictionary)
//! `fold` = `cata` (his `fold` alias agrees on the verb). `into_fold` =
//! cata over the owned base functor. [`Recursor`] ≈ Mendler-style
//! `mcata`/`mpara`, promoted from his Advanced section to the foundation
//! — subterm access is native, so `para` needs no separate scheme, and it
//! works over foreign types no `Base` instance could cover. `Base t` =
//! [`Recursive::Layer`]; `makeBaseFunctor` = `#[derive(Recursive)]`, with
//! the `F`-suffix convention traded for a `Layer` namespace. Banana-split
//! is [`Pair`] as the combinator and `banana` as the theorem. `cataA` =
//! carrier enrichment, which is what the `Env` parameter defunctionalizes
//! — the two are proved pointwise equal (`agreeV`/`agreeR`). `hylo`/
//! `refold` = [`Thunk`] holes: the coalgebra lives in the data, and
//! deforestation is measured, not assumed. `embed` = [`RecursiveOwned`],
//! with `cata embed = id` as `reflection` and [`Rebuild`]. What he ships
//! that this module deliberately does not: the distributive-law tower
//! (`gcata`..`zygoHistoPrepro`) — reachable here as user code over
//! [`Recursor`], named when a consumer names it first.
//!
//! # Laws
//! Mechanized in the accompanying Agda corpus (`FoldEnv.agda`, `--safe`,
//! no postulates); names below are its theorem names.
//!
//! * **recurrence**: `fold(node) = ascend . reduce(Layer(fold)) . descend`
//!   per edge, and `fold` is the unique such map (initiality) — for
//!   *strictly positive* `Layer`. Rust has no positivity checker; that an
//!   impl's `Layer` is a pattern functor of its tree is checked per impl
//!   (rim: `Box<dyn Fn(T) -> T>` fields break it silently).
//! * **balance** (`balV`/`balR`): with context motion owned by the
//!   bracketed driver and `reduce` context-silent, context evolution is a
//!   function of the term alone, for every algebra.
//! * **banana** (`bananaV`/`bananaR`): under the same condition, `Pair` in
//!   one traversal equals the two independent folds, unconditionally.
//! * **reflection** (`reflection`, `copy-and-analyze` in `Hylo.agda`):
//!   folding with `embed` is the identity ([`Rebuild`]); paired with any
//!   analysis it yields (copy, result) in one traversal.
//! * **absorption** (`absorb-sound`, `pair-short` in `Hylo.agda`): the
//!   short-circuiting driver equals the plain fold given the annihilation
//!   law, and one short-circuiting `Pair` pass equals the two counter-
//!   factual plain folds — the equation that gives the single runnable
//!   pass over affine codata (today: a [`PairOwned`] consuming pass) its
//!   meaning. Annihilation is inherited by
//!   `Pair` under the both-components predicate (`pair-annihilates`).
//!   Absorption × motion is now a theorem pair (`AbsorbEnv.agda`):
//!   `naive-leaks` — a Break that skips the restore corrupts the
//!   environment (counterexample); `balG` + `agree` — the GUARDED driver
//!   (restore on the bubble path) keeps balance on every path and equals
//!   the strict fold under annihilation. This is a hard constraint on
//!   future `#[scope]` codegen and on hand-written bracketed drivers:
//!   frame restoration belongs on the unwind path, guard-shaped, not
//!   sequenced after the child — and "early exit" includes panics.
//!   SHIPPED as `#[recursive(scope)]` + [`ScopedEnv`] + [`ScopeGuard`]:
//!   the generated `fold_in` brackets marked holes with a `Drop` guard,
//!   witnessed balanced on all three exits (normal, `Break`, panic) in
//!   `tests/witnesses.rs`. Field order is scoping order — order is
//!   contract. Mutual recursion is SHIPPED (`#[recursive_family]`,
//!   examples/mutual.rs): two-hole layers, family algebra trait, scoped
//!   drivers balanced across the sort boundary and through panic.
//!   Two-sorted absorption is SHIPPED (either-bubble + generated
//!   `Absorb` trait; sound under bubble-form annihilation —
//!   `TwoAbsorb.agda`, T-X — which the PROOF discovered: cross-sort
//!   bubbles need promotes that act as sections on absorbed values).
//!   Frame content from sibling folds is SHIPPED (`scope_prev` +
//!   [`ScopedEnvWith`] — over interior mutability: the husk lesson).
//!   Still open, by promotion doctrine: owned mutual drivers,
//!   single-sort `scope_prev`, the family positivity lint.
//!
//!   The `dyn` taxonomy (probe-witnessed): `&mut dyn FnMut` appears in
//!   two roles. In [`Recursor`]/[`Recursor2`] and `Thunk` it is
//!   LOAD-BEARING — the erased pass-manager face and heterogeneous
//!   closure storage respectively; keep. In the [`Holes`] family and the
//!   generated CPS drivers it is INCIDENTAL — those traits are already
//!   non-object-safe from their method generics, the recursion knot does
//!   not form (one closure instantiation per fold), erased algebras flow
//!   through generic-`F` holes unchanged, and the HRTB-over-GAT bound
//!   the un-`dyn`ed drivers need is accepted by rustc. A generic-`F`
//!   migration (the `cps::Piece`/`PieceDyn` split, applied to closures)
//!   is therefore POSSIBLE — and was CANCELLED by measurement
//!   (`benches/dyn_fence.rs`, one machine, one tree shape, min-of-7):
//!   on a 4M-node tree the `dyn` fold ran the cheap algebra at ~7.4
//!   ns/node vs ~15.5 for the transparent generic, tied on a heavier
//!   algebra, and the erased-algebra path degraded under generic holes.
//!   A generic variant with a manual `#[inline(never)]` fence matched
//!   `dyn` exactly, so the mechanism is the CALL FENCE: the virtual
//!   call stops LLVM from partially unrolling the recursion into
//!   i-cache bloat, and erasing it removes the fence. The `dyn` in the
//!   `Holes` family is therefore performance-load-bearing, not debt —
//!   the opposite of the intuition that demanded the benchmark, which
//!   is why the benchmark was demanded.
//!
//!   THE WALL, NAMED (§6 of the sqlfront report): the derive's family
//!   face is ANALYSIS-shaped — algebras get `&Env`, which is what makes
//!   [`Pair`] unconditional and frame-balance a theorem. A
//!   TRANSFORMATION that builds into an arena needs `&mut` effects; that
//!   is [`Recursor2`]'s face (`&mut Env`), not the derive's. Past two
//!   sorts, hand-write the `RecursorN` trait — and know the cost going
//!   in: a hand-written trait does not inherit the generated laws or the
//!   mechanized balance/agreement theorems. Routing an interning effect
//!   through interior mutability inside a `FoldAlg` env instead is the
//!   husk pattern; the crate declines to make it convenient.
//! * **silence is the price** (`collapseV`, `balance-fails`,
//!   `pair-not-banana`): a `reduce` that mutates the environment is legal
//!   but forfeits balance and poisons `Pair` — the first algebra's
//!   mutation leaks into the second's reads. Witnessed both ways:
//!   context-silent state algebras collapse to the pure model
//!   (transporting every law); a one-frame mutation counterexample breaks
//!   both laws.
//! * **well-scopedness** (`safeV`/`safeR`): resolution-style algebras
//!   using total-with-default lookup are junk on ill-scoped input; on
//!   well-scoped input a checked (`Option`-valued) algebra never fails and
//!   agrees with the total one. State the hypothesis or ship the check.
//!
//! **Analyses vs transformations**: borrowed layers optimize analyses
//! (resolve, typecheck, size, search). A REWRITE — a fold whose output is
//! the tree type itself — must rebuild nodes, and borrowed payloads force
//! a clone per kept payload. Rewriting folds use the consuming
//! `into_fold` over [`RecursiveOwned`]/[`IntoFoldAlg`] — payloads moved,
//! zero clones, shared structure rejected by the missing [`HolesMove`].
//! `embed` shipped ([`RecursiveOwned::embed`] over [`HolesWrap`], with
//! `reflection` as its theorem) and owned-`Pair` shipped ([`PairOwned`],
//! where owned unzip re-meets its [`crate::base::Comonoid`] price).
//! Still open: absorption on the consuming path — `into_fold` has no
//! `try` variant; short-circuits live on the borrowed drivers today.
//!
//! # Walls and deferred
//! * [`Recursor2`] hardcodes arity 2 on purpose: arity-*n* is indexed
//!   families — the first step up the HKT tower, out of scope with the
//!   crate-level receipt. A third mutually-recursive sort costs one more
//!   trait, written by hand, when a consumer brings one.
//! * Unfolds as EXPLICIT API (`ana : Coalg -> Seed -> Tree`) remain
//!   deferred — but hylo itself already shipped, internalized: a
//!   [`Thunk`]-holed tree IS a bundled (seed, coalgebra), and the plain
//!   fold over it is the deforested refold (measured in
//!   `examples/hylo.rs`). What waits for a consumer is the seed-first
//!   presentation and its `machines`-side dual, now one `wrap` away
//!   given [`RecursiveOwned::embed`].

/// Single-sorted recursor: the general fold face over a tree type `N`
/// with ambient environment `Env`.
///
/// The algebra receives the environment, the *unfolded* node, and the
/// recursion itself as a continuation. Descent decisions — including
/// environment updates at binder edges — happen inside `step`, where the
/// node's constructors are visible. Object-safe: `Box<dyn Recursor<..>>`
/// is the runtime-composed pass-manager face, no GAT tax.
///
/// # Law
/// The mutate-XOR-borrow discipline of [`crate::cps::Piece`] holds by the
/// same signature reasoning: `rec` takes `&mut Env` alongside a borrowed
/// node, so an output borrowing the environment is unrepresentable.
pub trait Recursor<N: ?Sized, Env: ?Sized> {
    /// The fold's result type at each node.
    type Out;
    /// One step: inspect `node`, recurse via `rec` as needed (bracketing
    /// any environment motion around the calls), and produce the result.
    fn step(
        &self,
        env: &mut Env,
        node: &N,
        rec: &mut dyn FnMut(&mut Env, &N) -> Self::Out,
    ) -> Self::Out;
}

/// Tie the knot for a [`Recursor`]: the generic driver, written once.
///
/// # Divergence
/// Recursion is structural ONLY if the reachable structure is finite and
/// acyclic. `Rc`/`Arc`-shared nodes can form knots (safe Rust, no
/// warning): a cycle has no leaves, so no algebra result ever forms, and
/// absorption cannot fire — only descent-side control inside `step` (a
/// fuel/visited check, see `examples/walls.rs`) can bail. Shared DAG
/// nodes are re-folded once per parent: worst case O(paths) = exponential
/// in depth; memoize by node identity in `Env` if that bites — advice
/// specific to THIS face, whose `Env` is `&mut`. The bracketed
/// [`FoldAlg`] face hands algebras `&Env` (which is what makes [`Pair`]
/// unconditional), so a memo there requires interior mutability inside
/// `Env` — relocated, not retired. If you need a memo, you want this
/// face.
pub fn run<N: ?Sized, Env: ?Sized, A>(alg: &A, env: &mut Env, node: &N) -> A::Out
where
    A: Recursor<N, Env> + ?Sized,
{
    alg.step(env, node, &mut |e, n| run(alg, e, n))
}

/// Two-sorted recursor: mutually recursive node types `N1`, `N2` (an
/// algebra for an endofunctor on the product category — both
/// continuations available at each step, so folds may cross the sort
/// boundary threading the same environment).
///
/// Open design gap: absorption/short-circuiting is single-sorted only.
/// A bubbled value has one type; crossing the `Out1`/`Out2` boundary
/// needs either unified outputs or an `Either`-shaped break channel —
/// undesigned, deliberately, until a two-sorted consumer needs it.
pub trait Recursor2<N1: ?Sized, N2: ?Sized, Env: ?Sized> {
    /// The fold's result at sort 1.
    type Out1;
    /// The fold's result at sort 2.
    type Out2;
    /// One step at sort 1; both sorts' recursions are available.
    fn step1(
        &self,
        env: &mut Env,
        node: &N1,
        rec1: &mut dyn FnMut(&mut Env, &N1) -> Self::Out1,
        rec2: &mut dyn FnMut(&mut Env, &N2) -> Self::Out2,
    ) -> Self::Out1;
    /// One step at sort 2; both sorts' recursions are available.
    fn step2(
        &self,
        env: &mut Env,
        node: &N2,
        rec1: &mut dyn FnMut(&mut Env, &N1) -> Self::Out1,
        rec2: &mut dyn FnMut(&mut Env, &N2) -> Self::Out2,
    ) -> Self::Out2;
}

/// Tie the knot for a [`Recursor2`] starting at sort 1.
///
/// # Divergence
/// Same conditions as [`run`]: finite acyclic reachable structure, or
/// descent-side control in the steps.
pub fn run1<N1: ?Sized, N2: ?Sized, Env: ?Sized, A>(alg: &A, env: &mut Env, node: &N1) -> A::Out1
where
    A: Recursor2<N1, N2, Env> + ?Sized,
{
    alg.step1(
        env,
        node,
        &mut |e, n| run1::<N1, N2, Env, A>(alg, e, n),
        &mut |e, n| run2::<N1, N2, Env, A>(alg, e, n),
    )
}

/// Tie the knot for a [`Recursor2`] starting at sort 2.
pub fn run2<N1: ?Sized, N2: ?Sized, Env: ?Sized, A>(alg: &A, env: &mut Env, node: &N2) -> A::Out2
where
    A: Recursor2<N1, N2, Env> + ?Sized,
{
    alg.step2(
        env,
        node,
        &mut |e, n| run1::<N1, N2, Env, A>(alg, e, n),
        &mut |e, n| run2::<N1, N2, Env, A>(alg, e, n),
    )
}

use core::ops::ControlFlow;

/// A tree type presented by its pattern functor: `Layer<T>` is the one-
/// level shape with recursive positions replaced by `T` (Lambek's lemma
/// says the tree is `Layer<Tree>`; only the destructor side is needed,
/// and it lives in the per-IR bracketed driver rather than here).
///
/// The GAT appears on THIS face only; [`Recursor`] does not pay it.
pub trait Recursive {
    /// The pattern functor at this sort. Borrows the node's payloads
    /// (`'a` is the tree borrow); recursive positions are `T`.
    type Layer<'a, T>
    where
        Self: 'a;
    /// Split a paired layer. Payloads are shared references, so this is
    /// bound-free: `&P` duplicates for nothing. Owned duplication — and
    /// its [`crate::base::Comonoid`] price — moved to the leaves, paid only when an
    /// algebra decides to keep a payload.
    ///
    /// # Hand-implementing
    /// Restate `where Self: 'a` on your impl's `unzip` (and on
    /// `FoldAlg::reduce`). Omitting it fails with `E0195: lifetime
    /// parameters or bounds ... do not match the trait declaration`,
    /// which does not name the missing bound — this note is that error's
    /// missing sentence.
    fn unzip<'a, A, B>(layer: Self::Layer<'a, (A, B)>) -> (Self::Layer<'a, A>, Self::Layer<'a, B>)
    where
        Self: 'a;
}

/// How recursive children sit inside a node: implemented in-crate for
/// `Box`, `Vec`, `Option`, `Rc`, `Arc`, `LazyCell`/`LazyLock` (shared
/// and lazy pointers get the borrowed family only — and the orphan rule
/// means only this crate could provide std impls at all). The derive's
/// classifier chains ANY single-argument wrapper terminating in `Self`,
/// so a custom owning pointer with a user-side `Holes` impl works as a
/// plain field, no attribute (probe-witnessed). The `{Box, Vec, Option,
/// Thunk}` list gates only the CONSUMING face: other wrappers — `Rc`,
/// `Arc`, custom pointers — fold borrowed-face-only until the
/// `#[recursive(movable)]` escape hatch exists. `#[recursive(hole)]` is
/// for the remaining case: an OPAQUE field type with no syntactic `Self`
/// inside (a newtyped id, a handle) whose `Hole` impl the classifier
/// cannot infer.
///
/// # Owning vs. denoting (credit: the sqlfront report)
/// A pointer OWNS its child — `&self` suffices to reach it. A handle
/// (an arena index, an interner id) DENOTES it: reaching the child needs
/// the arena, and no method here takes one; `HolesWrap::wrap` is worse —
/// for a hash-consed IR it would be interning, which needs `&mut Arena`
/// from a pure associated fn. These obligations are UNREPRESENTABLE for
/// handles, not merely awkward: an impl can only panic or smuggle the
/// arena through ambient state. Do not implement this family for handle
/// types. Index/handle IRs use the bracketed pattern instead: hand-write
/// [`Recursive`] with `Layer<'a, T>` borrowing payloads from the arena —
/// it works with [`Pair`], [`ScopeGuard`], and the whole borrowed face
/// (see the hand-implementation note on [`Recursive::unzip`]).
///
/// # Arena access: what exists, and the named remainder
/// The vocabulary is SHIPPED: [`HolesIn<T, Ar>`](HolesIn) (access only)
/// with the terminal-object blanket making plain containers the `Ar =
/// ()` fiber — see its docs for the probe-witnessed walls that shaped it
/// (E0050 kills retrofitting `Holes`; the ∀`Ar` blanket E0119-poisons;
/// only the `()` fiber is safe to make literal). `examples/arena.rs`
/// drives a hash-consed IR through it. The REMAINDER, awaiting its
/// consumer: derive support threading `&Ar` through generated drivers,
/// so handle IRs get `#[derive(Recursive)]` instead of the ten-line
/// hand driver. Consumption stays out (shared nodes cannot be consumed —
/// the forced-hole gate already says borrowed-face-only), and
/// construction stays out (interning is `&mut Ar` and the reflection
/// law becomes interning's fixed point — a rebuild design for
/// [`Recursor2`], not a `wrap`). Promotion trigger: a consumer for whom
/// the hand-written bracketed pattern costs real per-IR boilerplate.
///
/// The SHAPE of a hole container: how results sit once children are
/// folded, and how a shape of pairs splits — single-child pointers
/// collapse `Mapped<U>` to a bare `U` (the fold result needs no box),
/// sequences keep their shape. Deliberately capability-free
/// — `unzip_with` consumes a `Mapped`, never a container, so every
/// container has a shape even when it grants no access (this is what
/// lets [`Thunk`] participate in layers and pairs without borrowed
/// forcing existing at all).
pub trait Hole<T> {
    /// The container's shape with children replaced by results.
    type Mapped<U>;
    /// Split a shape of pairs into two shapes, via a per-element splitter
    /// (compositional: nested containers nest their splitters).
    fn unzip_with<P, A, B>(
        m: Self::Mapped<P>,
        split: &mut dyn FnMut(P) -> (A, B),
    ) -> (Self::Mapped<A>, Self::Mapped<B>);
}

/// Borrowed access to children: the analysis family's capability.
/// [`Thunk`] deliberately does NOT implement this — borrowed forcing was
/// removed because `&self` cannot speak an affine effect: it produced
/// husks that type-checked as reusable and panicked on refold. Codata
/// folds live on the consuming path, where a second fold is `E0382`.
pub trait Holes<T>: Hole<T> {
    /// Fold every child by reference, rebuilding the result shape.
    fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> Self::Mapped<U>;
    /// `map_ref` with early exit: `Break` abandons the remaining children
    /// (partial results drop — affine weakening makes abandonment free).
    fn try_map_ref<U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, Self::Mapped<U>>;
    /// The general early-exit map: the break type is independent of the
    /// element type — what a cross-sort bubble needs. Law: `try_map_ref`
    /// must equal `map_ref_until` at `B = U`.
    fn map_ref_until<B, U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, Self::Mapped<U>>;
}

/// Arena-indexed access: [`Holes`] fibered over an environment. A handle
/// DENOTES its child; reaching it needs the arena, so every method takes
/// one. Plain containers are the fiber over the terminal object — the
/// blanket below makes `Ar = ()` literal, so generic code can bind
/// `HolesIn<T, Ar>` uniformly over owning and denoting worlds.
///
/// Access ONLY, by design: consumption is impossible for shared nodes
/// regardless of arena access (sharedness, not arena-absence, is the
/// obstruction), and construction is interning (`&mut Ar`) — a rebuild
/// design belonging to [`Recursor2`], not a `wrap`.
///
/// # Laws
/// * exactly-once, in order, shape-preserving — the [`Holes`] access
///   laws, fibered: they must hold at every `Ar`.
/// * fiber coherence: at `Ar = ()` the blanket makes `map_ref_in` equal
///   `map_ref` definitionally — that impl IS the law.
/// * the arena is read-only here (`&Ar`); an impl must not observe
///   mutation it cannot see.
///
/// `try_map_ref_in` is deliberately absent: it is `map_ref_until_in` at
/// `B = U`, and this trait ships the general primitive only.
/// (`Ar = ()` default per house style: [`crate::cps::Piece`] established
/// env-parametrization-with-unit-default in this crate before this trait
/// existed — the stateless case names no environment.)
pub trait HolesIn<T, Ar: ?Sized = ()>: Hole<T> {
    /// Visit each child once, in order, reaching through the arena.
    fn map_ref_in<U>(&self, ar: &Ar, f: &mut dyn FnMut(&T) -> U) -> Self::Mapped<U>;
    /// The break-typed early-exit map, arena-threaded.
    fn map_ref_until_in<B, U>(
        &self,
        ar: &Ar,
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, Self::Mapped<U>>;
}

/// The terminal-object fiber, made literal (probe-witnessed: legal,
/// hybrid-compatible — a type may hold this AND an arena-specific impl —
/// unlike the `∀Ar` blanket, which E0119-poisons).
impl<T, W: Holes<T>> HolesIn<T, ()> for W {
    fn map_ref_in<U>(&self, _: &(), f: &mut dyn FnMut(&T) -> U) -> Self::Mapped<U> {
        self.map_ref(f)
    }
    fn map_ref_until_in<B, U>(
        &self,
        _: &(),
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, Self::Mapped<U>> {
        self.map_ref_until(f)
    }
}

// # Laws (Holes) — the extension-point contract
// * shape: `map_ref` preserves the container's shape; it calls `f` exactly
//   once per child, in order.
// * try/plain coherence: if `f` never breaks, `try_map_ref(f)` must equal
//   `Continue(map_ref(f'))` for the unwrapped `f'`.
// * unzip/map coherence: `unzip_with(map_ref(|c| (f(c), g(c))), id)` must
//   equal `(map_ref(f), map_ref(g))` up to shape.
// Third-party impls are trusted on these; they are what the fold's own
// laws (balance, banana, absorption) quantify over.
/// Implement [`Holes`] for a collapsing pointer via its `Deref`.
///
/// Piggybacks on `Deref<Target = T>`: `map_ref` is a deref, `Mapped<U>`
/// collapses to `U`, splitting is identity. A blanket impl is ruled out
/// by coherence (it would conflict with shaped containers), so the laws
/// live here, stated once, and each pointer costs one invocation:
/// `deref_holes! { [T] MyPtr<T> }`.
///
/// Scope is structural, not incidental: `Deref` is the interface of
/// call-by-NEED. Shaped containers (`Vec`, `Option`) fall outside because
/// `Deref` says nothing about shape; call-by-NAME (`Thunk`) falls outside
/// because `&self -> &Target` has nowhere for an unmemoized value to
/// live — `LazyCell` memoizes *because* `Deref` forces it to.
#[macro_export]
macro_rules! deref_holes {
    ([$($g:tt)*] $ty:ty) => {
        impl<$($g)*> $crate::cata::Hole<T> for $ty {
            type Mapped<U> = U;
            fn unzip_with<P, A, B>(m: P, split: &mut dyn FnMut(P) -> (A, B)) -> (A, B) {
                split(m)
            }
        }
        impl<$($g)*> $crate::cata::Holes<T> for $ty {
            fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> U {
                f(self)
            }
            fn try_map_ref<U>(
                &self,
                f: &mut dyn FnMut(&T) -> core::ops::ControlFlow<U, U>,
            ) -> core::ops::ControlFlow<U, U> {
                f(self)
            }
            fn map_ref_until<B, U>(
                &self,
                f: &mut dyn FnMut(&T) -> core::ops::ControlFlow<B, U>,
            ) -> core::ops::ControlFlow<B, U> {
                f(self)
            }
        }
    };
}

// Boxed child: the canonical single-child pointer.
deref_holes! { [T] alloc::boxed::Box<T> }
// Call-by-need child: forced on first fold, retained (deref forces).
// `LazyCell` is 1.80 = the crate floor (witnessed both directions) —
// `lazy` and accept the higher floor only if you actually fold need-cells.
deref_holes! { [T, F: FnOnce() -> T] core::cell::LazyCell<T, F> }
// Shared child (single-threaded). Recomputes per parent — memoize by
// node identity in the `Env` if that bites. WALL: reachable structure
// must be finite and acyclic; the fold diverges on a knot.
deref_holes! { [T] alloc::rc::Rc<T> }
// Shared child (thread-safe). Same recompute and acyclicity caveats.
deref_holes! { [T] alloc::sync::Arc<T> }
// Thread-safe call-by-need (std + lazy).
#[cfg(feature = "std")]
deref_holes! { [T, F: FnOnce() -> T] std::sync::LazyLock<T, F> }

/// Consuming access to children: the capability a rewrite needs and a
/// shared pointer cannot grant. `Rc`/`Arc`/`LazyCell` deliberately do NOT
/// implement this — the type system, not a doc note, is what says "you
/// cannot consume shared structure." For [`Thunk`] this makes single-
/// forcing STATIC: `map_move` takes the thunk by value, and since borrowed
/// forcing no longer exists, no double-force path exists at all.
// # Laws (Hole) — the shape contract
// * unzip preserves shape: `unzip_with(m, split)` yields two shapes each
//   congruent to `m`; `split` is called exactly once per element, in order.
// * identity coherence: `unzip_with(m, |p| (f(p), g(p)))` must equal the
//   pair of elementwise images — no element invented, dropped, or reused.
// # Laws (HolesMove) — the consuming contract
// * exactly-once, in order: `map_move` calls `f` once per child, in
//   declaration order; the result has the container's shape.
// * try/plain coherence: if `f` never breaks, `try_map_move(f)` equals
//   `Continue(map_move(f'))` for the unwrapped `f'`.
// * abandonment: on `Break`, remaining children are dropped UNCONSUMED —
//   over codata, unforced. Affine weakening makes this free; no partial
//   results escape.
// * move/borrow agreement (when `Holes` is also implemented): for pure
//   `f`, `c.map_move(f)` and `c.map_ref(|t| f-by-ref)` observe the same
//   children in the same order.
pub trait HolesMove<T>: Hole<T> {
    /// Fold every child by value, consuming the container.
    fn map_move<U>(self, f: &mut dyn FnMut(T) -> U) -> Self::Mapped<U>;
    /// `map_move` with early exit. On `Break`, remaining children are
    /// DROPPED UNCONSUMED — over codata, remaining thunks are never
    /// forced, so an error costs a path, not a tree.
    fn try_map_move<U>(
        self,
        f: &mut dyn FnMut(T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, Self::Mapped<U>>;
}

// # Laws (HolesMove) — the consuming contract
// * shape: `map_move` visits each child exactly once, in order, preserving
//   the container's shape; where a `Holes` impl also exists, `map_move`
//   over a container must agree with `map_ref` up to ownership (same
//   values, same order — witnessed by fold/into_fold agreement in the
//   test suite, unmechanized).
// * try/plain coherence: a never-breaking `f` makes `try_map_move` equal
//   `Continue(map_move(f'))`.
// * abandonment: on `Break`, remaining children drop UNCONSUMED — over
//   codata, unforced. Affine weakening makes this free; impls must not
//   force or visit past the break point.
impl<T> HolesMove<T> for alloc::boxed::Box<T> {
    fn map_move<U>(self, f: &mut dyn FnMut(T) -> U) -> U {
        f(*self)
    }
    fn try_map_move<U>(self, f: &mut dyn FnMut(T) -> ControlFlow<U, U>) -> ControlFlow<U, U> {
        f(*self)
    }
}
impl<T> HolesMove<T> for alloc::vec::Vec<T> {
    fn map_move<U>(self, f: &mut dyn FnMut(T) -> U) -> alloc::vec::Vec<U> {
        self.into_iter().map(f).collect()
    }
    fn try_map_move<U>(
        self,
        f: &mut dyn FnMut(T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, alloc::vec::Vec<U>> {
        let mut out = alloc::vec::Vec::with_capacity(self.len());
        for t in self {
            match f(t) {
                ControlFlow::Continue(u) => out.push(u),
                ControlFlow::Break(u) => return ControlFlow::Break(u),
            }
        }
        ControlFlow::Continue(out)
    }
}
impl<T> HolesMove<T> for Option<T> {
    fn map_move<U>(self, f: &mut dyn FnMut(T) -> U) -> Option<U> {
        self.map(f)
    }
    fn try_map_move<U>(
        self,
        f: &mut dyn FnMut(T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, Option<U>> {
        match self {
            None => ControlFlow::Continue(None),
            Some(t) => match f(t) {
                ControlFlow::Continue(u) => ControlFlow::Continue(Some(u)),
                ControlFlow::Break(u) => ControlFlow::Break(u),
            },
        }
    }
}
impl<T> HolesMove<T> for Thunk<T> {
    // Both takes are infallible post-sacrifice: with no borrowed forcing,
    // the only way to empty the cell is a by-value move that consumed self.
    fn map_move<U>(mut self, f: &mut dyn FnMut(T) -> U) -> U {
        let thunk = self
            .0
            .get_mut()
            .take()
            .expect("unreachable: Thunk consumed by value");
        f(thunk())
    }
    fn try_map_move<U>(mut self, f: &mut dyn FnMut(T) -> ControlFlow<U, U>) -> ControlFlow<U, U> {
        let thunk = self
            .0
            .get_mut()
            .take()
            .expect("unreachable: Thunk consumed by value");
        f(thunk())
    }
}

/// Constructing access: build the container around a finished child —
/// what `embed` (and eventually `ana`) needs. Completes a capability
/// lattice with principled asymmetries: `Rc`/`Arc` WRAP but cannot MOVE
/// (shared structure is constructible, not consumable); [`Thunk`] MOVES
/// but wraps only at `'static` (an already-forced value posing as a
/// thunk must own its captures); `LazyCell` does neither (no pre-forced
/// constructor exists — `Deref`'s memoization contract again). `Deref`
/// deliberately implies none of this: reading says nothing about
/// building, so `deref_holes!` does not generate it.
// # Laws (HolesWrap) — the construction contract
// * shape faithfulness: `wrap(m)` produces a container whose shape is
//   `m`'s; when `Holes` is also implemented, `wrap(m).map_ref(f)` equals
//   mapping `f` over `m` directly (elements preserved, in order); when
//   `HolesMove` is implemented, `wrap(m).map_move(f)` likewise.
// * with `unzip_with`: `wrap` distributes — wrapping then splitting
//   equals splitting then wrapping each side.
// * reflection is the composite law: these are what `cata embed = id`
//   (`reflection`, Hylo.agda) quantifies over per container.
pub trait HolesWrap<T>: Hole<T> {
    /// Wrap a finished child (or shaped collection of children).
    fn wrap(m: Self::Mapped<T>) -> Self;
}

// # Laws (HolesWrap) — the constructing contract
// * section: `wrap(m).map_ref(f)` must equal the elementwise image of `m`
//   under `f` (wrapping then reading is reading) — for collapsing
//   pointers this is `f(&t)`; for shaped containers, shape-congruent.
// * reflection: composed through a full layer, wrap chains are exactly
//   what makes `cata embed = id` (`reflection`, Hylo.agda; [`Rebuild`]).
// * codata caveat: `Thunk::wrap` produces an ALREADY-FORCED value in
//   thunk's clothing — lawful, but laziness is not preserved (see the
//   `Rebuild` caveats).
impl<T> HolesWrap<T> for alloc::boxed::Box<T> {
    fn wrap(m: T) -> Self {
        alloc::boxed::Box::new(m)
    }
}
impl<T> HolesWrap<T> for alloc::vec::Vec<T> {
    fn wrap(m: alloc::vec::Vec<T>) -> Self {
        m
    }
}
impl<T> HolesWrap<T> for Option<T> {
    fn wrap(m: Option<T>) -> Self {
        m
    }
}
impl<T> HolesWrap<T> for alloc::rc::Rc<T> {
    fn wrap(m: T) -> Self {
        alloc::rc::Rc::new(m)
    }
}
impl<T> HolesWrap<T> for alloc::sync::Arc<T> {
    fn wrap(m: T) -> Self {
        alloc::sync::Arc::new(m)
    }
}
impl<T: 'static> HolesWrap<T> for Thunk<T> {
    fn wrap(m: T) -> Self {
        Thunk::new(move || m)
    }
}

/// The owned pattern functor: payloads by value, for consuming folds.
/// Separate from [`Recursive`] so existing borrowed-only impls stand.
pub trait RecursiveOwned: Recursive {
    /// One level with owned payloads and recursive positions as `T`.
    type LayerOwned<T>;
    /// Lambek's constructor half: rebuild one node from a filled layer.
    fn embed(layer: Self::LayerOwned<Self>) -> Self
    where
        Self: Sized;
    /// Biased split for mixed pairs: children pairs separate for free;
    /// payloads are LENT to the continuation (the analysis side) and then
    /// MOVED into the returned owned layer (the transformation side).
    /// Zero duplication — the Comonoid bound predicted here never
    /// materializes, because the pair is biased instead of symmetric.
    /// (Two-TRANSFORMATION pairs need real payload duplication; that
    /// stays user-level, with the dup at the leaf that wants it.)
    /// Machinery, not API: exists to serve [`PairOwned`]; call that
    /// instead. Hidden from docs — a public HRTB-bearing generic is a
    /// compatibility promise nobody asked for (burntsushi's rule: if
    /// users see `for<'x>` in an error, the API is wrong).
    #[doc(hidden)]
    /// `'static` bounds: the continuation's layer borrows locals inside
    /// the split, so the closure is lifetime-polymorphic; under the GAT's
    /// implied bounds that means the tree and the analysis output must
    /// outlive every lifetime. Arena-borrowing IRs are excluded here (as
    /// they already are from the derive) — a named wall, not an accident.
    fn split_with<A, B, O>(
        layer: Self::LayerOwned<(A, B)>,
        k: &mut dyn for<'x> FnMut(Self::Layer<'x, B>) -> O,
    ) -> (Self::LayerOwned<A>, O)
    where
        Self: Sized + 'static,
        B: 'static;
}

/// An environment with scope structure: the driver calls `enter` before
/// descending into a `#[recursive(scope)]`-marked hole and `exit` on the
/// way out. The `Frame` is a restoration token — typically a snapshot
/// (saved depth, saved length) that `exit` truncates to, exactly the
/// model mechanized in `AbsorbEnv.agda`.
pub trait ScopedEnv {
    /// Restoration token captured on entry.
    type Frame;
    /// Descend into a binder: push/extend, return the restore token.
    fn enter(&mut self) -> Self::Frame;
    /// Leave the binder: restore from the token. Called on EVERY exit —
    /// normal return, absorption `Break`, or panic — via [`ScopeGuard`].
    fn exit(&mut self, frame: Self::Frame);
}

/// The snapshot model, shipped (§3 of the sqlfront report: every
/// consumer's first ten lines were this impl behind an E0117 newtype).
/// A scope stack IS a `Vec`; frames are length snapshots — exactly what
/// `AbsorbEnv.agda` mechanizes.
impl<T> ScopedEnv for alloc::vec::Vec<T> {
    type Frame = usize;
    fn enter(&mut self) -> usize {
        self.len()
    }
    fn exit(&mut self, saved: usize) {
        self.truncate(saved);
    }
}

impl<T> ScopedEnv for alloc::collections::VecDeque<T> {
    type Frame = usize;
    fn enter(&mut self) -> usize {
        self.len()
    }
    fn exit(&mut self, saved: usize) {
        self.truncate(saved);
    }
}

/// Scope entry that carries CONTENT: the frame is derived from a sibling
/// binding — the preceding field's folded value (a relation's columns) or
/// payload. This is the resolver pattern: `#[recursive(scope_prev)]` in a
/// family marks a hole whose scope is fed by what came just before it in
/// declaration order (order is contract). Chosen over interior-mutable
/// envs deliberately: algebras keep reading `&Env`, and no affine effect
/// is laundered through a shared borrow — the husk lesson, applied.
pub trait ScopedEnvWith<I: ?Sized>: ScopedEnv {
    /// Enter a scope whose frame is built from `info`.
    fn enter_with(&mut self, info: &I) -> Self::Frame;
}

/// The theorem, made borrow-checkable: frame restoration on the unwind
/// path. `naive-leaks` (AbsorbEnv.agda) shows a `Break` that skips the
/// restore corrupts the environment; `balG`/`agree` show the guarded
/// driver is balanced on every path and equal to the strict fold under
/// annihilation. A `Drop` guard is the only shape that covers all three
/// exits (normal, `Break`, panic) with one code path.
pub struct ScopeGuard<'e, E: ScopedEnv + ?Sized> {
    env: &'e mut E,
    frame: Option<E::Frame>,
}

impl<'e, E: ScopedEnv + ?Sized> ScopeGuard<'e, E> {
    /// Enter a scope, arming restoration.
    pub fn new(env: &'e mut E) -> Self {
        let frame = env.enter();
        ScopeGuard {
            env,
            frame: Some(frame),
        }
    }
    /// Arm restoration for a frame already entered (the content-carrying
    /// path: `enter_with` first, then guard).
    ///
    /// ORDER IS THE CONTRACT: take the frame BEFORE mutating the env. A
    /// snapshot taken after a push records the grown stack, and the push
    /// leaks on exit — the guard restores whatever frame it is handed
    /// (`brkAb` proves that much; WHICH frame is your obligation).
    /// [`ScopedEnvWith::enter_with`] packages the ordering atomically;
    /// prefer it when the frame carries content.
    pub fn from_frame(env: &'e mut E, frame: E::Frame) -> Self {
        ScopeGuard {
            env,
            frame: Some(frame),
        }
    }
    /// Access the environment while the scope is open.
    pub fn env(&mut self) -> &mut E {
        self.env
    }
}

impl<'e, E: ScopedEnv + ?Sized> Drop for ScopeGuard<'e, E> {
    fn drop(&mut self) {
        if let Some(f) = self.frame.take() {
            self.env.exit(f);
        }
    }
}

/// Mixed pair: one consuming transformation + one borrowed analysis, one
/// traversal. The analysis sees the INPUT tree (pre-rewrite payloads and
/// structure), the transformation consumes it.
///
/// # Law
/// `t.into_fold(&e, &PairOwned(Rebuild, g)) == (t, t.fold(&e, &g))` —
/// the copy-and-analyze law (`copy-and-analyze` in `Hylo.agda`): pairing
/// the identity rewrite with any analysis yields the tree back alongside
/// the analysis, in one pass. Every rewrite+analysis pair is a
/// perturbation of it.
///
/// A both-consuming pair (two transformations, one pass) is deliberately
/// absent: both algebras would want the owned payloads, so the pair
/// must duplicate them — the [`crate::base::Comonoid`] toll this module
/// exists to dodge. Pay it explicitly instead: clone the tree, or run
/// two passes. (The consistent future shape, if a consumer names it, is
/// a pair GATED on payload `Comonoid` — priced duplication, the house
/// pattern — not a refusal.)
#[must_use = "an algebra does nothing until a tree is folded with it"]
#[derive(Debug, Clone, Copy, Default)]
pub struct PairOwned<F, G>(F, G);

/// Free-function door for [`PairOwned`] — **unbounded**, unlike
/// [`IntoFoldAlg::pair_owned`], so it stays inference-transparent: a
/// tree-polymorphic algebra like [`Rebuild`] can be paired here without
/// pinning `R`/`Env` at the construction site (the method form must
/// select an impl to be called at all; the fold pins the types later
/// either way).
pub fn pair_owned<F, G>(f: F, g: G) -> PairOwned<F, G> {
    PairOwned(f, g)
}

impl<R, Env, F, G> IntoFoldAlg<R, Env> for PairOwned<F, G>
where
    R: RecursiveOwned + 'static,
    Env: ?Sized,
    F: IntoFoldAlg<R, Env>,
    G: FoldAlg<R, Env>,
    G::Out: 'static,
{
    type Out = (F::Out, G::Out);
    fn reduce(&self, env: &Env, layer: R::LayerOwned<(F::Out, G::Out)>) -> Self::Out {
        let (la, g) = R::split_with(layer, &mut |lb| self.1.reduce(env, lb));
        (self.0.reduce(env, la), g)
    }
    fn absorbing(&self, out: &Self::Out) -> bool {
        // forced, not conservative: same argument as `Pair::absorbing`
        self.0.absorbing(&out.0) && self.1.absorbing(&out.1)
    }
}

/// The identity rewrite: fold with `embed` as the algebra.
///
/// # Law (reflection)
/// `t.into_fold(&env, &Rebuild) == t` — the fold that rebuilds every node
/// is the identity (mechanized: `reflection` in `Hylo.agda`). This is the
/// zero point every rewrite is a perturbation of.
///
/// Two codata caveats: the law is denotational — over [`Thunk`] holes,
/// `Rebuild` forces everything and re-wraps values in trivial thunks, so
/// the *identity* preserves the tree and destroys its laziness. And over
/// an INFINITE codata tree, `Rebuild` never absorbs, so
/// `PairOwned(Rebuild, search)` diverges where the search alone would
/// terminate — pairing with the identity forfeits
/// termination-by-annihilation.
#[derive(Debug, Clone, Copy, Default)]
pub struct Rebuild;

impl<R: RecursiveOwned, Env: ?Sized> IntoFoldAlg<R, Env> for Rebuild {
    type Out = R;
    fn reduce(&self, _env: &Env, layer: R::LayerOwned<R>) -> R {
        R::embed(layer)
    }
}

/// Bottom-up algebra over OWNED layers: the transformation family.
/// Payloads arrive by value — a rewrite (`Out = Self`-the-tree) reuses
/// them with zero clones, which is what closes the analyses-vs-
/// transformations gap for the motivating consumer's rewrite passes.
pub trait IntoFoldAlg<R: RecursiveOwned + ?Sized, Env: ?Sized> {
    /// The synthesized result (for rewrites: the tree type itself).
    type Out;
    /// Reduce one owned layer of already-folded children.
    fn reduce(&self, env: &Env, layer: R::LayerOwned<Self::Out>) -> Self::Out;
    /// Absorbing element, as on [`FoldAlg::absorbing`]; same annihilation
    /// law, same theorems. Over codata, a `Break` on this path drops the
    /// remaining thunks unconsumed — and unforced.
    fn absorbing(&self, _out: &Self::Out) -> bool {
        false
    }

    /// Banana-split at the owned grade — build [`PairOwned`]: `self`
    /// consumes the payloads, `g` (a borrowing [`FoldAlg`]) reads them.
    fn pair_owned<G>(self, g: G) -> PairOwned<Self, G>
    where
        Self: Sized,
    {
        PairOwned(self, g)
    }
}

impl<T> Hole<T> for alloc::vec::Vec<T> {
    type Mapped<U> = alloc::vec::Vec<U>;
    fn unzip_with<P, A, B>(
        m: alloc::vec::Vec<P>,
        split: &mut dyn FnMut(P) -> (A, B),
    ) -> (alloc::vec::Vec<A>, alloc::vec::Vec<B>) {
        let mut xs = alloc::vec::Vec::with_capacity(m.len());
        let mut ys = alloc::vec::Vec::with_capacity(m.len());
        for p in m {
            let (a, b) = split(p);
            xs.push(a);
            ys.push(b);
        }
        (xs, ys)
    }
}

impl<T> Holes<T> for alloc::vec::Vec<T> {
    fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> alloc::vec::Vec<U> {
        self.iter().map(f).collect()
    }
    fn try_map_ref<U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, alloc::vec::Vec<U>> {
        self.map_ref_until(f)
    }
    fn map_ref_until<B, U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, alloc::vec::Vec<U>> {
        let mut out = alloc::vec::Vec::with_capacity(self.len());
        for t in self {
            match f(t) {
                ControlFlow::Continue(u) => out.push(u),
                ControlFlow::Break(b) => return ControlFlow::Break(b), // partials drop
            }
        }
        ControlFlow::Continue(out)
    }
}

impl<T> Hole<T> for Option<T> {
    type Mapped<U> = Option<U>;
    fn unzip_with<P, A, B>(
        m: Option<P>,
        split: &mut dyn FnMut(P) -> (A, B),
    ) -> (Option<A>, Option<B>) {
        match m {
            None => (None, None),
            Some(p) => {
                let (a, b) = split(p);
                (Some(a), Some(b))
            }
        }
    }
}

impl<T> Holes<T> for Option<T> {
    fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> Option<U> {
        self.as_ref().map(&mut *f)
    }
    fn try_map_ref<U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, Option<U>> {
        self.map_ref_until(f)
    }
    fn map_ref_until<B, U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, Option<U>> {
        match self.as_ref() {
            None => ControlFlow::Continue(None),
            Some(t) => match f(t) {
                ControlFlow::Continue(u) => ControlFlow::Continue(Some(u)),
                ControlFlow::Break(b) => ControlFlow::Break(b),
            },
        }
    }
}

/// A codata hole: a child *produced on demand* by a one-shot closure,
/// folded, and dropped before the parent continues. A tree whose
/// recursive positions are `Thunk`s is a bundled (seed, coalgebra) — the
/// generated `fold` over it is a **deforested hylomorphism**: the
/// intermediate tree never exists in full; peak liveness is one root-to-
/// leaf path.
///
/// Forcing is affine — each thunk runs once, and since the sacrifice this
/// is enforced by the type system: forcing happens only through by-value
/// moves. Corollary: two passes over the same codata **must** fuse, and
/// the fusion combinator is [`PairOwned`] — not an optimization but the
/// only way to run a second pass, since the tree no longer exists after
/// the first.
///
/// **Consuming-only, by design.** `Thunk` implements [`HolesMove`] and
/// NOT [`Holes`]: borrowed forcing existed briefly and was removed —
/// `&self` cannot speak an affine effect, so it produced husks that
/// type-checked as reusable and panicked on refold (a runtime `take`).
/// On the consuming path, forcing is by-value: a second fold is `E0382`,
/// and the affine protocol is enforced by the checker, not a panic.
/// Codata folds therefore go through `into_fold`; two passes over the
/// same codata fuse via [`PairOwned`].
///
/// For call-by-NEED (memoized, subtree retained) use `LazyCell`/`LazyLock`
/// holes below instead.
///
/// Whitelist wrinkle (macro-inherent): the derive matches the bare IDENT
/// `Thunk` — proc-macros are resolution-blind — so a foreign type merely
/// NAMED `Thunk` is classified as codata (consuming-only) by the derive.
/// Rename or use the via-form if that bites.
pub struct Thunk<T>(core::cell::Cell<Option<alloc::boxed::Box<dyn FnOnce() -> T>>>);

impl<T> core::fmt::Debug for Thunk<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // deliberately opaque: peeking would force or reveal consumption
        f.write_str("Thunk(..)")
    }
}

impl<T> Thunk<T> {
    /// Wrap a one-shot producer.
    pub fn new(f: impl FnOnce() -> T + 'static) -> Self {
        Thunk(core::cell::Cell::new(Some(alloc::boxed::Box::new(f))))
    }
}

impl<T> Hole<T> for Thunk<T> {
    type Mapped<U> = U;
    fn unzip_with<P, A, B>(m: P, split: &mut dyn FnMut(P) -> (A, B)) -> (A, B) {
        split(m)
    }
}

// Removed: `ThunkSend` (the Send-producer codata cell) — shipped under
// "crate polish" with zero consumers, which is the `dfa` standard
// unmet and the doctrine this crate applies to others' requests
// (HolesIn's own docs decline surface without a consumer). One test
// existed only because the zero-coverage sweep wrote it. Restorable
// additively the day someone threads a codata tree across threads;
// the impl was: Cell<Option<Box<dyn FnOnce() -> T + Send>>>, consuming-
// only per the husk sacrifice, HolesWrap at T: Send + 'static.

/// Memoization slot without a stored producer: folds as a maybe-present
/// child (`Mapped<U> = Option<U>`) — you cannot force what has no thunk.
impl<T> Hole<T> for core::cell::OnceCell<T> {
    type Mapped<U> = Option<U>;
    fn unzip_with<P, A, B>(
        m: Option<P>,
        split: &mut dyn FnMut(P) -> (A, B),
    ) -> (Option<A>, Option<B>) {
        match m {
            None => (None, None),
            Some(p) => {
                let (a, b) = split(p);
                (Some(a), Some(b))
            }
        }
    }
}

impl<T> Holes<T> for core::cell::OnceCell<T> {
    fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> Option<U> {
        self.get().map(&mut *f)
    }
    fn try_map_ref<U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<U, U>,
    ) -> ControlFlow<U, Option<U>> {
        self.map_ref_until(f)
    }
    fn map_ref_until<B, U>(
        &self,
        f: &mut dyn FnMut(&T) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, Option<U>> {
        match self.get() {
            None => ControlFlow::Continue(None),
            Some(t) => match f(t) {
                ControlFlow::Continue(u) => ControlFlow::Continue(Some(u)),
                ControlFlow::Break(b) => ControlFlow::Break(b),
            },
        }
    }
}

/// Bottom-up algebra over a [`Recursive`]'s layers, with read-only access
/// to the environment.
///
/// # Law
/// Read-only `&Env` is the *silence* condition under which balance and
/// banana hold (see module laws). An algebra that needs to mutate the
/// environment belongs in a [`Recursor`] step instead, and knowingly
/// forfeits [`Pair`].
pub trait FoldAlg<R: Recursive + ?Sized, Env: ?Sized> {
    /// The synthesized result.
    type Out;
    /// Reduce one layer of already-folded children. Payloads arrive
    /// borrowed; keeping one is the algebra's decision and the algebra's
    /// price. Lifetime-generic, so the erased `dyn FoldAlg` face survives.
    fn reduce<'a>(&self, env: &Env, layer: R::Layer<'a, Self::Out>) -> Self::Out
    where
        R: 'a;
    /// Is this value the carrier's absorbing element? (Terminology:
    /// unrelated to [`crate::base::Absorb`], which is a sink — the
    /// algebra action of the free–forgetful adjunction. THIS is the
    /// annihilator sense: for a [`crate::ringy::Semiring`] carrier the
    /// canonical instance is `|x| *x == S::zero()`, since `zero`
    /// annihilates `⊗` by that trait's own law — the sqlfront report's
    /// dialect-feasibility algebra is exactly this shape.) Absorbing children
    /// bubble to the fold's result immediately; remaining children are not
    /// folded (over codata: not even forced). `Err`, `None`, or a lattice
    /// top all work — fallibility is a property of the carrier, not a
    /// second trait.
    ///
    /// # Law (annihilation)
    /// If `absorbing(x)`, then for any layer containing `x` in a hole,
    /// the intended `reduce` must equal `x` — skipping it is sound
    /// (mechanized: `absorb-sound`, `pair-short` in `Hylo.agda`).
    fn absorbing(&self, _out: &Self::Out) -> bool {
        false
    }

    /// Banana-split with a second algebra — build [`Pair`]: one
    /// traversal, both results.
    fn pair<G>(self, g: G) -> Pair<Self, G>
    where
        Self: Sized,
    {
        Pair(self, g)
    }

    /// Weaken to any environment — build [`AtAny`] (defined when this
    /// algebra's `Env = ()`).
    fn at_any(self) -> AtAny<Self>
    where
        Self: Sized,
    {
        AtAny(self)
    }
}

/// A shared reference to an algebra is an algebra — reuse one algebra
/// across folds and [`Pair`]s without moving or cloning it:
/// `(&a).pair(&b)` composes borrowed. (Advanced-usage gap, closed: every
/// method already took `&self`; only the blanket was missing.)
impl<R: Recursive + ?Sized, Env: ?Sized, A: FoldAlg<R, Env>> FoldAlg<R, Env> for &A {
    type Out = A::Out;
    fn reduce<'a>(&self, env: &Env, layer: R::Layer<'a, Self::Out>) -> Self::Out
    where
        R: 'a,
    {
        (*self).reduce(env, layer)
    }
    fn absorbing(&self, out: &Self::Out) -> bool {
        (*self).absorbing(out)
    }
}

/// The consuming mirror of the `&A` [`FoldAlg`] blanket.
impl<R: RecursiveOwned + ?Sized, Env: ?Sized, A: IntoFoldAlg<R, Env>> IntoFoldAlg<R, Env> for &A {
    type Out = A::Out;
    fn reduce(&self, env: &Env, layer: R::LayerOwned<Self::Out>) -> Self::Out {
        (*self).reduce(env, layer)
    }
    fn absorbing(&self, out: &Self::Out) -> bool {
        (*self).absorbing(out)
    }
}

/// Weakening: run an environment-free algebra at any environment.
///
/// Affine weakening is free at the value level (drop the env); this
/// adapter is the same fact at the trait level, as a newtype because a
/// blanket impl would collide with direct impls under coherence.
/// Composes with [`Pair`]: `Pair(env_using, AtAny(env_free))` is the
/// common one-traversal shape.
#[must_use = "an algebra does nothing until a tree is folded with it"]
#[derive(Debug, Clone, Copy, Default)]
pub struct AtAny<F>(F);

/// Free-function door for [`AtAny`] — unbounded, inference-transparent
/// (see [`pair_owned`]).
pub fn at_any<F>(f: F) -> AtAny<F> {
    AtAny(f)
}

impl<R, Env, F> FoldAlg<R, Env> for AtAny<F>
where
    R: Recursive + ?Sized,
    Env: ?Sized,
    F: FoldAlg<R, ()>,
{
    type Out = F::Out;
    fn reduce<'a>(&self, _env: &Env, layer: R::Layer<'a, Self::Out>) -> Self::Out
    where
        R: 'a,
    {
        self.0.reduce(&(), layer)
    }
    fn absorbing(&self, out: &Self::Out) -> bool {
        self.0.absorbing(out)
    }
}

/// Banana-split: run both algebras in one traversal.
///
/// # Law
/// `fold(Pair(f, g)) = (fold(f), fold(g))` — unconditionally, because
/// [`FoldAlg`] cannot touch the environment (Agda: `bananaV`/`bananaR`;
/// and `pair-not-banana` for why the restriction is load-bearing).
///
/// This concept exists at three grades in this crate, with the
/// duplication toll placed exactly where each grade forces it:
/// [`crate::base::Pair`] (sinks) and
/// [`crate::machines::DuplicateToMachine`] (the Moore product) both
/// duplicate the token, paying [`crate::base::Comonoid`]/`Unaliased`;
/// THIS `Pair` is the fold grade, where the layer is lent by reference
/// and the toll is dodged entirely — the banana-as-signature story.
/// Same product, three prices.
#[must_use = "an algebra does nothing until a tree is folded with it"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Pair<F, G>(F, G);

/// Free-function door for [`Pair`] — unbounded (see [`pair_owned`] for
/// why the free forms exist beside the methods: inference transparency
/// for tree-polymorphic algebras, plus the symmetric reading).
pub fn pair<F, G>(f: F, g: G) -> Pair<F, G> {
    Pair(f, g)
}

impl<R, Env, F, G> FoldAlg<R, Env> for Pair<F, G>
where
    R: Recursive + ?Sized,
    Env: ?Sized,
    F: FoldAlg<R, Env>,
    G: FoldAlg<R, Env>,
{
    type Out = (F::Out, G::Out);
    fn reduce<'a>(&self, env: &Env, layer: R::Layer<'a, (F::Out, G::Out)>) -> Self::Out
    where
        R: 'a,
    {
        let (lf, lg) = R::unzip(layer);
        (self.0.reduce(env, lf), self.1.reduce(env, lg))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;

    // Single-sorted smoke tree; payload bound shows where Comonoid bites.
    enum Tree {
        Leaf(u32),
        Node(Box<Tree>, Box<Tree>),
    }
    enum TreeLayer<'a, T> {
        Leaf(&'a u32),
        Node(T, T),
    }
    impl Recursive for Tree {
        type Layer<'a, T> = TreeLayer<'a, T>;
        fn unzip<'a, A, B>(l: TreeLayer<'a, (A, B)>) -> (TreeLayer<'a, A>, TreeLayer<'a, B>)
        where
            Self: 'a,
        {
            match l {
                // payload is a shared reference: duplication is free
                TreeLayer::Leaf(p) => (TreeLayer::Leaf(p), TreeLayer::Leaf(p)),
                TreeLayer::Node((a1, a2), (b1, b2)) => {
                    (TreeLayer::Node(a1, b1), TreeLayer::Node(a2, b2))
                }
            }
        }
    }

    // per-IR bracketed driver over a FoldAlg (env: max-depth budget check)
    fn fold<Env: ?Sized, A: FoldAlg<Tree, Env> + ?Sized>(a: &A, env: &Env, t: &Tree) -> A::Out {
        match t {
            Tree::Leaf(p) => a.reduce(env, TreeLayer::Leaf(p)),
            Tree::Node(l, r) => {
                let l = fold(a, env, l);
                let r = fold(a, env, r);
                a.reduce(env, TreeLayer::Node(l, r))
            }
        }
    }

    struct Sum;
    impl FoldAlg<Tree, ()> for Sum {
        type Out = u32;
        fn reduce<'a>(&self, _: &(), l: TreeLayer<'a, u32>) -> u32
        where
            Tree: 'a,
        {
            match l {
                TreeLayer::Leaf(p) => *p,
                TreeLayer::Node(a, b) => a + b,
            }
        }
    }
    struct Depth;
    impl FoldAlg<Tree, ()> for Depth {
        type Out = u32;
        fn reduce<'a>(&self, _: &(), l: TreeLayer<'a, u32>) -> u32
        where
            Tree: 'a,
        {
            match l {
                TreeLayer::Leaf(_) => 0,
                TreeLayer::Node(a, b) => 1 + a.max(b),
            }
        }
    }

    // env-carrying single-sorted recursor: depth-indexed leaf weighting
    struct Weighted;
    impl Recursor<Tree, u32> for Weighted {
        type Out = u32;
        fn step(
            &self,
            env: &mut u32,
            n: &Tree,
            rec: &mut dyn FnMut(&mut u32, &Tree) -> u32,
        ) -> u32 {
            match n {
                Tree::Leaf(p) => *p + *env,
                Tree::Node(a, b) => {
                    *env += 1; // descend
                    let s = rec(env, a) + rec(env, b);
                    *env -= 1; // ascend
                    s
                }
            }
        }
    }

    // ---- defunctionalized fold: the cata as an actual machines::Machine ----
    // State = (depth env, stack of pending outputs, open-bracket count).
    // Input alphabet: Open (the descent edge, PRE-children — its necessity
    // is the `blind` lemma in stream form), Leaf(payload), Close (the
    // ascent + reduce, post-children). Readout is Moore-stable: Some(fold)
    // iff the tokens so far form exactly one complete tree.
    enum Tok {
        Open,
        Leaf(u32),
        Close,
    }
    struct FoldMachine {
        depth: u32,
        stack: alloc::vec::Vec<u32>,
        open: usize,
        wedged: bool, // ill-formed stream seen (stack underflow)
    }
    impl FoldMachine {
        fn new() -> Self {
            FoldMachine {
                depth: 0,
                stack: alloc::vec::Vec::new(),
                open: 0,
                wedged: false,
            }
        }
    }
    impl crate::machines::Machine for FoldMachine {
        type In = Tok;
        type Out = Option<u32>;
        fn out(&self) -> Option<u32> {
            if !self.wedged && self.open == 0 && self.stack.len() == 1 {
                Some(self.stack[0]) // readout duplicates the top: Copy here,
            } else {
                // Comonoid in general — the fourth sighting.
                None
            }
        }
        fn update(&mut self, i: Tok) {
            if self.wedged {
                return;
            }
            match i {
                Tok::Open => {
                    self.depth += 1; // descend: BEFORE children, hence pre-order token
                    self.open += 1;
                }
                Tok::Leaf(p) => self.stack.push(p + self.depth),
                Tok::Close => {
                    let (b, a) = match (self.stack.pop(), self.stack.pop()) {
                        (Some(b), Some(a)) => (b, a),
                        _ => {
                            self.wedged = true;
                            return;
                        }
                    };
                    self.depth -= 1; // ascend
                    self.open -= 1;
                    self.stack.push(a + b); // reduce(Node)
                }
            }
        }
    }

    fn tokenize(t: &Tree, out: &mut alloc::vec::Vec<Tok>) {
        match t {
            Tree::Leaf(p) => out.push(Tok::Leaf(*p)),
            Tree::Node(a, b) => {
                out.push(Tok::Open);
                tokenize(a, out);
                tokenize(b, out);
                out.push(Tok::Close);
            }
        }
    }

    #[test]
    fn machine_agrees_with_recursive_fold() {
        use crate::machines::Machine;
        let t = Tree::Node(
            Box::new(Tree::Leaf(1)),
            Box::new(Tree::Node(Box::new(Tree::Leaf(2)), Box::new(Tree::Leaf(3)))),
        );
        let mut toks = alloc::vec::Vec::new();
        tokenize(&t, &mut toks);
        let mut m = FoldMachine::new();
        for tok in toks {
            assert_eq!(m.out(), None, "no readout mid-tree");
            m.update(tok);
        }
        let mut depth = 0u32;
        assert_eq!(m.out(), Some(run(&Weighted, &mut depth, &t)));
        assert_eq!(m.depth, 0, "machine env restored, same balance");
    }

    #[test]
    fn machine_is_stack_safe_where_recursion_is_not() {
        use crate::machines::Machine;
        // Left spine 50_000 deep, no tree materialized at all: the token
        // stream is generated iteratively. The recursive `run` would eat
        // 50k call frames; the machine's stack is a Vec.
        const N: u32 = 50_000;
        let mut m = FoldMachine::new();
        for _ in 0..N {
            m.update(Tok::Open);
        }
        m.update(Tok::Leaf(1)); // innermost leaf, depth N
        for _ in 0..N {
            m.update(Tok::Leaf(1)); // right leaf at each level
            m.update(Tok::Close);
        }
        // expected: (1 + N) + sum_{i=1..N} (1 + i)
        let expected = (1 + N) + N + N * (N + 1) / 2;
        assert_eq!(m.out(), Some(expected));
    }

    // Two-sorted recursor: previously shipped with ZERO in-crate usage —
    // unverified public surface, caught by the overkill audit. A minimal
    // mutually-recursive pair (statements/expressions) exercises the
    // cross-sort continuation threading and the dyn face.
    enum Stmt {
        Say(#[allow(dead_code)] u32),
        If(Box<Ex>, Box<Stmt>),
    }
    enum Ex {
        #[allow(dead_code)]
        Lit(u32),
        Block(Box<Stmt>),
    }
    struct CountBoth;
    impl Recursor2<Stmt, Ex, u32> for CountBoth {
        type Out1 = u32;
        type Out2 = u32;
        fn step1(
            &self,
            env: &mut u32,
            n: &Stmt,
            rec1: &mut dyn FnMut(&mut u32, &Stmt) -> u32,
            rec2: &mut dyn FnMut(&mut u32, &Ex) -> u32,
        ) -> u32 {
            *env += 1;
            match n {
                Stmt::Say(_) => 1,
                Stmt::If(c, b) => 1 + rec2(env, c) + rec1(env, b),
            }
        }
        fn step2(
            &self,
            env: &mut u32,
            n: &Ex,
            rec1: &mut dyn FnMut(&mut u32, &Stmt) -> u32,
            _rec2: &mut dyn FnMut(&mut u32, &Ex) -> u32,
        ) -> u32 {
            *env += 1;
            match n {
                Ex::Lit(_) => 1,
                Ex::Block(s) => 1 + rec1(env, s),
            }
        }
    }

    #[test]
    fn recursor2_crosses_sorts_and_threads_env() {
        // if (block { say 1 }) { say 2 }
        let s = Stmt::If(
            Box::new(Ex::Block(Box::new(Stmt::Say(1)))),
            Box::new(Stmt::Say(2)),
        );
        let mut visits = 0u32;
        assert_eq!(run1(&CountBoth, &mut visits, &s), 4);
        assert_eq!(visits, 4, "env threaded across the sort boundary");
        let b: alloc::boxed::Box<dyn Recursor2<Stmt, Ex, u32, Out1 = u32, Out2 = u32>> =
            alloc::boxed::Box::new(CountBoth);
        let mut v2 = 0u32;
        assert_eq!(run1(b.as_ref(), &mut v2, &s), 4);
    }

    #[test]
    fn banana_split_one_traversal() {
        let t = Tree::Node(
            Box::new(Tree::Leaf(1)),
            Box::new(Tree::Node(Box::new(Tree::Leaf(2)), Box::new(Tree::Leaf(3)))),
        );
        assert_eq!(fold(&Pair(Sum, Depth), &(), &t), (6, 2));
        // weakening: the same env-free algebras at a non-unit Env
        assert_eq!(fold(&Pair(AtAny(Sum), AtAny(Depth)), &7u32, &t), (6, 2));
        // dyn face on the FoldAlg side
        let b: Box<dyn FoldAlg<Tree, (), Out = u32>> = Box::new(Sum);
        assert_eq!(fold(b.as_ref(), &(), &t), 6);
    }

    #[test]
    fn recursor_threads_and_restores_env() {
        let t = Tree::Node(
            Box::new(Tree::Leaf(1)),
            Box::new(Tree::Node(Box::new(Tree::Leaf(2)), Box::new(Tree::Leaf(3)))),
        );
        let mut depth = 0u32;
        assert_eq!(run(&Weighted, &mut depth, &t), 11);
        assert_eq!(depth, 0, "ascend restored the environment");
        // dyn face on the Recursor side
        let b: Box<dyn Recursor<Tree, u32, Out = u32>> = Box::new(Weighted);
        let mut d2 = 0u32;
        assert_eq!(run(b.as_ref(), &mut d2, &t), 11);
    }
}
