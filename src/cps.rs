//! Push-encoded morphisms with an ambient mutable environment: the CPS face
//! of [`crate::base::Piece`].
//!
//! A [`Piece`] hands its outputs to a continuation instead of returning
//! them: `run(env, a, k)` pushes zero or more `&Out` into `k`, which may
//! stop the traversal with [`ControlFlow::Break`]. Denotationally this adds
//! nothing over [`crate::base::Piece`] — for a single emission,
//! `∀R. (Out → R) → R ≅ Out` (Yoneda) — the value is operational:
//!
//! * **Borrowed outputs** — the continuation receives `&Out` valid for the
//!   call, so a stage can lend into its input (children of a tree node)
//!   without cloning. A returning `Piece` must move or clone its output.
//! * **Multi-output** — a stage may emit `0..n` times, which makes this the
//!   list-arrow / nondeterminism grade (HXT's `a -> [b]`, push-encoded).
//! * **Ambient state** — the environment (an arena, an interner, a diagnostic
//!   sink) threads *through the continuation*: each stage borrows it mutably,
//!   then relinquishes it to `k`. No stage holds state in a return type.
//!
//! # The mutate-XOR-borrow law is in the signature
//! `k: FnMut(&mut Env, &Out)` receives the environment and the item
//! *together*, so an `Out` that borrows from `Env` is unrepresentable: the
//! impl would need `&mut env` and a `&`-into-env live at once, and the borrow
//! checker rejects it. The discipline this enforces — **mutating stages yield
//! indices (owned tokens); reads against the environment happen inside the
//! continuation** — is the same reasoning as [`crate::data::Visit`] taking
//! `&mut self`, promoted from convention to law. Borrows *along the input
//! chain* (a node lending its children) remain free and zero-clone.
//!
//! # Two faces, one trait
//! * [`Piece::run`] is generic over the break type `R` — fusing,
//!   zero-cost, **not object-safe** (a generic method has no vtable slot;
//!   the same trade as [`crate::data::Visit`]'s `visit<R>`).
//! * [`PieceDyn`] is the erased view: `R` pinned to `()`, obtained by blanket
//!   — every `Piece` is a `PieceDyn` for free. `Box<dyn PieceDyn>` is the
//!   runtime-composed pass manager / compiled-query case. The blanket is the
//!   only impl `PieceDyn` should ever have: it is a view, not an extension
//!   point.
//!
//! Because the environment appears in the continuation, one trait serves both
//! shapes this module was promoted for: tree-query filters run at `Env = ()`
//! (a ZST — the parameter costs nothing), and compiler pipelines run at
//! `Env = Arena`. See `examples/xml_filters.rs` for the former and this
//! module's `env_threads_through_continuation` test for the latter.
//!
//! What stays outside: a *composite* borrowed output
//! (`type Out<'a>` — a struct of references into the input) needs a lending
//! GAT, which forfeits `dyn` — the same wall as [`crate::data::MapMut`].
//! This module keeps `Out: ?Sized` non-generic so the erased face exists;
//! the lending face is a separate, deferred design.

use core::ops::ControlFlow;

/// A push-encoded morphism over an ambient environment. See the module docs
/// for the design; the shortest statement is: [`crate::base::Piece`] with the
/// return channel replaced by a continuation, the environment threaded
/// through that continuation, and `0..n` emissions allowed.
///
/// `Env` defaults to `()` for stateless filters.
pub trait Piece<A: ?Sized, Env: ?Sized = ()> {
    /// The output type pushed to the continuation (`?Sized`: `str` and slices
    /// are fine). Must not borrow from `Env` — unrepresentable by
    /// construction — and must not be a composite of input borrows (the
    /// lending wall; see module docs).
    type Out: ?Sized;

    /// Feed `a` through this stage, pushing each output into `k` together
    /// with the environment. Propagate `k`'s [`ControlFlow::Break`] to stop
    /// the whole traversal.
    fn run<R>(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &Self::Out) -> ControlFlow<R>,
    ) -> ControlFlow<R>;

    // --- Provided combinator methods (the `Iterator` form; mirrors
    // [`crate::base::Piece`]). Erasure unaffected: [`PieceDyn`] is the
    // object-safe face either way. ---

    /// `self` then `g`: every output of `self` feeds `g` — build [`Link`].
    fn link<G: Piece<Self::Out, Env>>(self, g: G) -> Link<Self, G>
    where
        Self: Sized,
    {
        Link(self, g)
    }
    /// `self` or `g`: both run on the input, outputs concatenated — build
    /// [`Both`]. Also a free function ([`both`]) for the symmetric reading.
    fn both<G: Piece<A, Env, Out = Self::Out>>(self, g: G) -> Both<Self, G>
    where
        Self: Sized,
    {
        Both(self, g)
    }
}

/// **Union** `f <+> g` — build [`Both`]. The free-function form of a
/// symmetric operation (the `std::iter::zip` precedent; see
/// [`crate::base::alongside`]): neither arm is privileged as receiver.
pub fn both<A: ?Sized, Env: ?Sized, F, G>(f: F, g: G) -> Both<F, G>
where
    F: Piece<A, Env>,
    G: Piece<A, Env, Out = <F as Piece<A, Env>>::Out>,
{
    Both(f, g)
}

/// Sequential composition — each output of `F` feeds `G`, results stream in
/// order; the list-arrow `>>>`. The continuation-nesting lives here, once.
#[must_use = "stages are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Link<F, G>(F, G);

impl<A: ?Sized, Env: ?Sized, F, G> Piece<A, Env> for Link<F, G>
where
    F: Piece<A, Env>,
    G: Piece<<F as Piece<A, Env>>::Out, Env>,
{
    type Out = G::Out;
    fn run<R>(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &G::Out) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        self.0.run(env, a, &mut |env, b| self.1.run(env, b, k))
    }
}

/// Union — both stages run on the same input, outputs concatenated in order
/// (HXT's `<+>`). Both must emit the same `Out`.
#[must_use = "stages are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Both<F, G>(F, G);

impl<A: ?Sized, Env: ?Sized, F, G> Piece<A, Env> for Both<F, G>
where
    F: Piece<A, Env>,
    G: Piece<A, Env, Out = <F as Piece<A, Env>>::Out>,
{
    type Out = F::Out;
    fn run<R>(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &F::Out) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        self.0.run(env, a, k)?;
        self.1.run(env, a, k)
    }
}

/// Embed a pure closure into a single-emission stage: the unit of the CPS
/// view, and the Yoneda embedding made concrete — `Embed(f)` calls `k` exactly
/// once with `f(a)`. Mirrors [`crate::base::Embed`] (same role,
/// this category). The closure sees neither `Env` nor the continuation;
/// env-aware stages implement [`Piece`] directly.
#[derive(Clone, Copy, Default)]
pub struct Embed<F>(pub F);
// `Debug` without an `F: Debug` bound (std's `Map` pattern; mirrors
// [`crate::base::Embed`]).
impl<F> core::fmt::Debug for Embed<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Embed").finish_non_exhaustive()
    }
}

impl<A: ?Sized, Env: ?Sized, B, F> Piece<A, Env> for Embed<F>
where
    F: Fn(&A) -> B,
{
    type Out = B;
    fn run<R>(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &B) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        k(env, &(self.0)(a))
    }
}

/// A shared reference to a stage is a stage — compose without moving
/// (mirrors [`crate::base::Piece`]'s `&M` impl; its absence here was a
/// composition gap: borrowed stages could not enter pipelines).
impl<A: ?Sized, Env: ?Sized, M: Piece<A, Env>> Piece<A, Env> for &M {
    type Out = M::Out;
    fn run<R>(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &Self::Out) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        (*self).run(env, a, k)
    }
}

/// The erased, object-safe face: [`Piece`] with the break type pinned to
/// `()`. Obtained by blanket — every `Piece` is a `PieceDyn` for free, so
/// `Box<dyn PieceDyn<A, Env, Out = B>>` is always available for runtime-
/// composed pipelines (pass managers, queries compiled from strings).
///
/// `ControlFlow<()>` rather than plain `()` because a pass manager wants
/// abort, and the sum is free.
///
/// Do not implement this directly: it is a *view* of [`Piece`], kept
/// blanket-only so the two faces can never disagree.
pub trait PieceDyn<A: ?Sized, Env: ?Sized = ()> {
    /// The output type; equal to the underlying [`Piece::Out`].
    type Out: ?Sized;
    /// [`Piece::run`] at `R = ()`.
    fn run_dyn(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &Self::Out) -> ControlFlow<()>,
    ) -> ControlFlow<()>;
}

impl<A: ?Sized, Env: ?Sized, M: Piece<A, Env>> PieceDyn<A, Env> for M {
    type Out = M::Out;
    fn run_dyn(
        &self,
        env: &mut Env,
        a: &A,
        k: &mut dyn FnMut(&mut Env, &Self::Out) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        self.run(env, a, k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;

    // A multi-output leaf: emit each element of a slice (Env-agnostic).
    struct Each;
    impl Piece<[u32]> for Each {
        type Out = u32;
        fn run<R>(
            &self,
            env: &mut (),
            a: &[u32],
            k: &mut dyn FnMut(&mut (), &u32) -> ControlFlow<R>,
        ) -> ControlFlow<R> {
            for x in a {
                k(env, x)?;
            }
            ControlFlow::Continue(())
        }
    }

    #[test]
    fn then_composes_by_continuation() {
        // Each >>> (+1): multi-output through a lifted pure stage.
        let pipe = Each.link(Embed(|x: &u32| x + 1));
        let mut got = Vec::new();
        let _: ControlFlow<()> = pipe.run(&mut (), &[1, 2, 3][..], &mut |_, y| {
            got.push(*y);
            ControlFlow::Continue(())
        });
        assert_eq!(got, [2, 3, 4]);
    }

    #[test]
    fn break_short_circuits_the_whole_pipeline() {
        let pipe = Each.both(Each); // union: would emit six
        let mut n = 0;
        let out: ControlFlow<u32> = pipe.run(&mut (), &[7, 8, 9][..], &mut |_, x| {
            n += 1;
            if n == 2 {
                ControlFlow::Break(*x)
            } else {
                ControlFlow::Continue(())
            }
        });
        assert_eq!(out, ControlFlow::Break(8)); // stopped inside the FIRST branch
        assert_eq!(n, 2);
    }

    #[test]
    fn lift_is_the_yoneda_embedding() {
        // Embed(f) calls k exactly once with f(a): CPS adds nothing denotational.
        let f = |x: &u32| x * 10;
        let mut calls = 0;
        let mut got = 0;
        let _: ControlFlow<()> = Embed(f).run(&mut (), &4, &mut |_, y| {
            calls += 1;
            got = *y;
            ControlFlow::Continue(())
        });
        assert_eq!((calls, got), (1, f(&4)));
    }

    // The ambient-environment face: Env = a mini interner (Vec<String>).
    // The stage MUTATES env and yields an INDEX — it cannot yield a borrow
    // into env (unrepresentable: k takes &mut Env alongside the item), so the
    // mutate-XOR-borrow law is enforced by the compiler, not by discipline.
    struct Intern;
    impl Piece<str, Vec<String>> for Intern {
        type Out = usize;
        fn run<R>(
            &self,
            env: &mut Vec<String>,
            a: &str,
            k: &mut dyn FnMut(&mut Vec<String>, &usize) -> ControlFlow<R>,
        ) -> ControlFlow<R> {
            let ix = env.len();
            env.push(a.to_string());
            k(env, &ix)
        }
    }

    #[test]
    fn env_threads_through_continuation() {
        let mut arena: Vec<String> = Vec::new();
        let mut seen = None;
        let _: ControlFlow<()> = Intern.run(&mut arena, "hello", &mut |env, &ix| {
            // reads against the environment happen HERE, in the continuation
            seen = Some(env[ix].clone());
            ControlFlow::Continue(())
        });
        assert_eq!(seen.as_deref(), Some("hello"));
        assert_eq!(arena, ["hello"]);
    }

    #[test]
    fn every_cps_morph_is_a_dyn_pass() {
        // the blanket at work: box the GENERIC stage as the ERASED face.
        let boxed: Box<dyn PieceDyn<[u32], (), Out = u32>> = Box::new(Each);
        let mut sum = 0;
        let _ = boxed.run_dyn(&mut (), &[1, 2, 3][..], &mut |_, x| {
            sum += x;
            ControlFlow::Continue(())
        });
        assert_eq!(sum, 6);
    }
}
