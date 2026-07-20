//! # `data` — polynomials as containers
//!
//! Graded consuming functors, the lawful in-place story, the box-free
//! monoidal (`zip`) presentation of Applicative, and **both** stream
//! encodings — visitor (final) and iterator (initial) — with the boundary
//! between them priced by theorem rather than discovered by issue tracker.

extern crate alloc;
use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::base::{Absorb, Comonoid, ControlFlow};

// ---- internal impl macros: collapse the mechanical functor families ----

/// Single-slot functor: one `.map`-style method yields MapMut + MapOnce.
/// Caller supplies the output type constructor as a closure over `B`.
macro_rules! functor1 {
    ($src:ty => $dst:ty, $map:ident, <$($p:ident),*>) => {
        impl<A $(, $p)*> MapMut<A> for $src {
            type Output<B> = $dst;
            fn fmap<B>(self, f: impl FnMut(A) -> B) -> Self::Output<B> { self.$map(f) }
        }
        impl<A $(, $p)*> MapOnce<A> for $src {
            fn fmap_once<B>(self, f: impl FnOnce(A) -> B) -> Self::Output<B> { self.$map(f) }
        }
    };
}

/// Sequence functor: MapMut via `into_iter().map().collect()`.
macro_rules! functor_seq {
    ($src:ty => $dst:ty) => {
        impl<A> MapMut<A> for $src {
            type Output<B> = $dst;
            fn fmap<B>(self, f: impl FnMut(A) -> B) -> Self::Output<B> {
                self.into_iter().map(f).collect()
            }
        }
    };
}

// ====================== Graded consuming functors ======================
//
// Foreclosed: one Functor trait with a uniform closure bound (the
// `higher`-crate design, `F: Fn(A) -> B` everywhere). The uniform bound
// over-demands: it makes `Option`'s fmap strictly weaker than
// `std::option::Option::map` (which takes `FnOnce`) and forbids stateful
// closures over `Vec` (which needs only `FnMut`). The closure grade is
// the comonoid requirement on the mapping function's captures, and it
// varies per instance — so it must live per trait, not per method.
// Two traits, ratified over a single grade-indexed trait for simplicity;
// a grade-generic bridge is additive later.

/// Refinement of [`MapMut`] for containers with **≤ 1 element slot**:
/// the map is invoked at most once, so the strongest caller interface —
/// `FnOnce`, closures that consume their captures — is sound.
///
/// # Laws
/// * identity and composition as in [`MapMut`], for `fmap_once`.
/// * coherence with the supertrait: `x.fmap_once(f) == x.fmap(f)`
///   whenever `f` is `FnMut` — the grades agree where both apply.
///
/// Method-name note: `fmap`, not `map` — an extension-trait `map`
/// silently loses to inherent methods (`Option::map`, `Iterator::map`)
/// during method resolution, a divergence hazard.
pub trait MapOnce<A>: MapMut<A> {
    /// Map with a closure that may consume its captures. Distinct name per
    /// the Fn-hierarchy precedent (`call_once`/`call_mut`): a shared name
    /// across the grades would make every call site ambiguous, and a
    /// blanket-impl subsumption is ruled out by coherence — with `A` as a
    /// trait parameter, downstream crates can legally instantiate it with
    /// a local type over a foreign carrier, so the overlap is real.
    /// Subsumption is therefore a supertrait bound: every `MapOnce`
    /// carrier is a `MapMut` carrier (`FnMut: FnOnce`), enforced by the
    /// bound and discharged by a small manual impl per type — the only
    /// impls this forecloses are unlawful ones, since on a ≤1-slot
    /// carrier the graded behaviors are extensionally forced equal.
    fn fmap_once<B>(self, f: impl FnOnce(A) -> B) -> Self::Output<B>;
}

/// Functor whose map is invoked **sequentially, possibly many times**.
/// The `FnMut` grade demands the captures survive repeated calls (a
/// comonoid condition on the environment) but still permits state.
///
/// # Laws
/// Identity and composition as in [`MapOnce`]; for stateful closures the
/// composition law holds with the states threaded in sequence.
/// **Not object-safe**: `fmap<B>` is generic and `Output<B>` is a GAT, so
/// there is no `dyn MapMut`. This is inherent to a shape-changing functor;
/// runtime polymorphism needs a monomorphic erasing wrapper. (`Machine`,
/// `Transducer`, `Piece`, `Absorb` *are* object-safe.)
pub trait MapMut<A> {
    /// The type family `F<B>`: same carrier, new parameter.
    type Output<B>;
    /// Map, consuming `self`; the closure may run many times.
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Self::Output<B>;
}

functor1!(Option<A> => Option<B>, map, <>);
functor1!(Result<A, E> => Result<B, E>, map, <E>);
/// Arrays map length-preservingly via `core::array::map` — the one functor
/// where the output length is fixed by the type, so `into_iter().collect()`
/// (which cannot target `[U; N]`) is the wrong tool.
impl<A, const N: usize> MapMut<A> for [A; N] {
    type Output<B> = [B; N];
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> [B; N] {
        self.map(f)
    }
}

// Box maps through deref, not a `.map` method — one line either way:
// Removed: `functor1!(core::task::Poll<A> => ...)` — a functor instance
// for the async tier that `machines` explicitly DEFERS (the Pin wall);
// an instance ahead of its own design. Returns with the async-machine
// tier, additively.
impl<A> MapMut<A> for Box<A> {
    type Output<B> = Box<B>;
    fn fmap<B>(self, mut f: impl FnMut(A) -> B) -> Box<B> {
        Box::new(f(*self))
    }
}
impl<A> MapOnce<A> for Box<A> {
    fn fmap_once<B>(self, f: impl FnOnce(A) -> B) -> Box<B> {
        Box::new(f(*self))
    }
}
functor_seq!(alloc::collections::VecDeque<A> => alloc::collections::VecDeque<B>);
impl<A> MapMut<A> for Vec<A> {
    type Output<B> = Vec<B>;
    /// # In-place note (behavior, not contract)
    /// `self` is owned, hence unique, so when source and target layouts
    /// match this compiles to an allocation-reusing map (std's in-place
    /// collect). That reuse rides on **unstable std internals**
    /// (specialization) and is therefore stated as observed behavior and
    /// pinned by a *canary* test — never promised. Whether
    /// pointer-comparison across an ownership transfer even means what it
    /// appears to is itself a provenance question; the canary is an early
    /// warning, not a law.
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Vec<B> {
        self.into_iter().map(f).collect()
    }
}

/// Endo-map in place: the optimized transport of a pure `fmap`, licensed
/// by `&mut`'s uniqueness proof.
///
/// # Law (this one *is* a law)
/// `map_in_place(&mut xs, f)` ≡
/// `xs = take(xs).fmap(|mut a| { f(&mut a); a })` — mutation through a
/// unique reference is observationally a pure function on values
/// (RustHorn's prophecy-pair model of `&mut` is the formal statement).
///
/// # Future directions
/// Pearlite annotations discharging this law in Creusot; laws are kept in
/// one greppable doc format so the annotation step stays mechanical.
pub fn map_in_place<A>(xs: &mut [A], mut f: impl FnMut(&mut A)) {
    for a in xs.iter_mut() {
        f(a);
    }
}

// ============================ Monoidal Zip ============================
//
// Applicative in its lax-monoidal presentation: `zip`, not `<*>`.
//
// Foreclosed: the `<*>` presentation (`F<A -> B>` applied to `F<A>`).
// A container *of functions* reifies the exponential inside F, and Rust
// has no exponential objects without boxing — this is precisely where
// `higher`'s `ApplyFn = Box<dyn Fn>` comes from. In a CCC the two
// presentations are interderivable by currying; Rust breaks exactly that
// equivalence, so the crate takes the presentation with no exponential
// anywhere. Governing dichotomy (inductive over every case met so far):
// closures as *arguments* are free; closures as *inhabitants* are boxed.
//
// The trait is binary (`Zip<A, B>`) so that duplication costs land
// per-instance, per-parameter, in the impl bounds where they are true —
// rather than boxed away uniformly for everyone.

/// The unit of an applicative: `pure : A -> F<A>` — the identity for
/// [`Zip`] up to the unit isomorphism `F<((), A)> ≅ F<A>`. Split from
/// `Zip` because not every lawful `Zip` has a `pure`: [`ZipVec`]'s would
/// be the infinite repetition, unrepresentable in a finite carrier (the
/// `Apply`-not-`Applicative` distinction, made a type).
pub trait Pointed<A> {
    /// `F<A>` for this carrier.
    type Wrap;
    /// Lift a value into the carrier (the applicative unit).
    fn pure(a: A) -> Self::Wrap;
}

/// The monoidal structure map `(F<A>, F<B>) -> F<(A, B)>`: pair two
/// structures of the same carrier into one over tupled elements.
///
/// # Laws
/// * associativity up to reassociation:
///   `zip(zip(a, b), c)` mapped by `((x, y), z) -> (x, (y, z))` equals
///   `zip(a, zip(b, c))`.
/// * unit laws with `pure` where an instance provides one.
///
/// **Not object-safe** (associated types `Rhs`/`Zipped` plus the pairing
/// shape). Use concretely.
///
/// # Foreclosed: per-value carriers
/// `Rhs`/`Zipped` are associated types, which assumes one carrier
/// *family*. Futures cannot implement this trait — every future is its
/// own type, and `join` pairs two *different* carriers. `Zip` is therefore
/// container-scoped; the effect-level zip belongs to the machine spine (an
/// effectful-transducer join), not here. Widening `Rhs` to a type parameter
/// would break this scoping, so the trait keeps it associated.
///
/// # Future directions
/// * `traverse` — deferred by decision. Both futures are additive: a
///   concrete `try_map` family, and/or the brand-generic
///   `traverse::<F, _, _>` (witnessed compiling on stable; pays the
///   mandatory-annotation tax at every call because a concrete value has
///   multiple brand decompositions and no solver can choose one).
/// * generic `lift_a2` (needs a Map bound on `FAB`; bound-plumbing
///   deferred with it).
pub trait Zip<A, B> {
    /// `F<B>` for the same carrier — the right-hand side of the
    /// structure map (the `Add<Rhs>` convention).
    type Rhs;
    /// `F<(A, B)>` for the same carrier.
    type Zipped;
    /// Pair two structures into one over tupled elements.
    fn zip(self, other: Self::Rhs) -> Self::Zipped;
}

/// Single slot: no duplication needed — works for non-`Clone` types.
impl<A, B> Zip<A, B> for Option<A> {
    type Rhs = Option<B>;
    type Zipped = Option<(A, B)>;
    fn zip(self, other: Option<B>) -> Option<(A, B)> {
        self.zip(other)
    }
}

/// `Result` zip: short-circuit on the first `Err` — the most common
/// applicative in Rust, single-slot so no duplication bound.
impl<A, B, E> Zip<A, B> for Result<A, E> {
    type Rhs = Result<B, E>;
    type Zipped = Result<(A, B), E>;
    fn zip(self, other: Result<B, E>) -> Result<(A, B), E> {
        Ok((self?, other?))
    }
}

impl<A> Pointed<A> for Option<A> {
    type Wrap = Option<A>;
    fn pure(a: A) -> Option<A> {
        Some(a)
    }
}
impl<A, E> Pointed<A> for Result<A, E> {
    type Wrap = Result<A, E>;
    fn pure(a: A) -> Result<A, E> {
        Ok(a)
    }
}
impl<A> Pointed<A> for Vec<A> {
    type Wrap = Vec<A>;
    fn pure(a: A) -> Vec<A> {
        alloc::vec![a]
    }
}

/// The cartesian product — THE list applicative. Materializes |a|·|b|
/// pairs, so its duplication cost is visible in the bounds instead of
/// hidden: `A` is duplicated per column, and each row duplicates the
/// whole `other` vector (`Vec<B>: Comonoid`, i.e. `B: Clone` through the
/// blanket — `B: Comonoid` alone cannot duplicate out of storage because
/// `dup` takes ownership).
impl<A: Comonoid, B> Zip<A, B> for Vec<A>
where
    Vec<B>: Comonoid,
{
    type Rhs = Vec<B>;
    type Zipped = Vec<(A, B)>;
    fn zip(self, mut ys: Vec<B>) -> Vec<(A, B)> {
        let mut out = Vec::with_capacity(self.len() * ys.len());
        let n = self.len();
        for (i, a) in self.into_iter().enumerate() {
            let row = if i + 1 < n {
                let (row, keep) = ys.dup();
                ys = keep;
                row
            } else {
                core::mem::take(&mut ys)
            };
            let m = row.len();
            let mut a = Some(a);
            for (j, b) in row.into_iter().enumerate() {
                // SAFETY(panic-free): `a` is set to `Some` before the loop and
                // re-`Some`d on every iteration except the last, and each
                // iteration `take`s then restores it; so `a` is `Some` at
                // every `unwrap` here. The final iteration leaves it `None`,
                // which the loop never revisits.
                let give = if j + 1 < m {
                    let (keep, give) = a.take().unwrap().dup();
                    a = Some(keep);
                    give
                } else {
                    a.take().unwrap()
                };
                out.push((give, b));
            }
        }
        out
    }
}

/// Total element-wise zip of arrays: length is equal by construction (both
/// `N`), so unlike [`ZipVec`] there is no truncation — the *total* monoidal
/// structure. No duplication bound.
impl<A, B, const N: usize> Zip<A, B> for [A; N] {
    type Rhs = [B; N];
    type Zipped = [(A, B); N];
    fn zip(self, other: [B; N]) -> [(A, B); N] {
        let mut b = other.into_iter();
        // SAFETY(panic-free): `self.map` calls the closure exactly N times,
        // and `b` is an into_iter over `[B; N]` yielding exactly N items, so
        // `next()` is `Some` on every call. Length equality is by type.
        self.map(|a| (a, b.next().unwrap()))
    }
}

/// Same carrier, second monoidal structure: element-wise, truncating
/// ("ZipList"). **No duplication bounds at all** — non-`Clone` elements
/// welcome. One carrier, two lawful `Zip`s: the structure is a choice,
/// not a property.
///
/// Vocabulary note (semigroupoids-style honesty): this instance is
/// `Apply`, **not** `Applicative` — a lawful `pure` would be the infinite
/// repetition, which a strict finite carrier cannot represent. The unit is
/// absent by theorem, not omission.
pub struct ZipVec<A>(
    /// Public on purpose (the carrier exception, cf.
    /// [`crate::base::Pair`]): the wrapper *is* a `Vec` wearing its
    /// second monoidal structure, and `.0` is how the vector goes in and
    /// comes back out.
    pub Vec<A>,
);
impl<A, B> Zip<A, B> for ZipVec<A> {
    type Rhs = ZipVec<B>;
    type Zipped = ZipVec<(A, B)>;
    fn zip(self, other: ZipVec<B>) -> ZipVec<(A, B)> {
        ZipVec(self.0.into_iter().zip(other.0).collect())
    }
}

/// Drive a visitor into an accumulator: the counit of the free–forgetful
/// adjunction made code, and the crate's data↔kernel seam.
///
/// ```
/// use affine_cat::data::{accumulate, ArrayWindows};
/// use affine_cat::base::{Count, Pair};
/// // one pass, two algebras: collect bigrams AND count them
/// let text = b"abcd";
/// let Pair(grams, n): Pair<Vec<[u8; 2]>, Count> =
///     accumulate(&mut ArrayWindows::<2>, &text[..]);
/// assert_eq!(grams, vec![[b'a', b'b'], [b'b', b'c'], [b'c', b'd']]);
/// assert_eq!(n.0, 3);
/// ```
pub fn accumulate<I, V, A>(v: &mut V, input: I) -> A
where
    V: Visit<I>,
    A: Absorb<V::Item> + Default,
{
    let mut acc = A::default();
    v.for_each(input, |t| acc.absorb(t));
    acc
}

// ======================= Streams: both encodings =======================
//
// A stream of token groups has two presentations:
//
// * **final / visitor** ([`Visit`]): internal iteration, the stream given
//   by its eliminator. Easiest to *implement* (creature_feature's core
//   insight), fuses producer and consumer with no intermediate structure.
// * **initial / iterator**: external iteration, `std::iter::Iterator` and
//   the machines in [`crate::machines`].
//
// **The boundary, priced (this is a theorem, not a preference):**
// concatenation/fanout-shaped combinators compose in the final encoding;
// **zip-shaped combinators do not** — pairing the k-th element of one
// push-stream with the (k+gap)-th of another requires suspending a
// producer, which is exactly the power internal iteration forfeits.
// (Observed in the wild as creature_feature issue #3: `GapGram` could not
// be generalized from `IterFtzr` to `Ftzr` — "it got hairy quick".)
// Consequently zip/gap-shaped combinators in this crate bound the
// *initial* side only, and that restriction is a documented wall, not a
// missing feature. The cheap bridge direction is initial → final
// (drive the iterator, push its items); the reverse is the expensive one.

/// The final (visitor) encoding of a token-group stream over `Input`.
///
/// `ControlFlow` from day one: the continuation can stop the traversal
/// (find-first, `take(n)`) and carry a residual — std's `for_each` vs
/// `try_fold` lesson applied at birth, because this signature is the most
/// semver-permanent object in the module.
///
/// # Foreclosed
/// * `FnMut(Item)` with no return (the creature_feature signature): no
///   early exit, no fallible sinks; retrofitting `ControlFlow` later
///   would be the breaking change this crate is designed never to need.
/// * Implementing zip-shaped combinators over `Visit` — see the boundary
///   note above.
///
/// # Future directions
/// * a `FromVisit`-style accumulator trait (the Moore/`Accumulates`
///   shape) fusing visitation with accumulation, one pass, two outputs.
/// * initial→final adapter structs for iterator-backed sources.
///
/// **Not object-safe**: `visit<R>` is generic over the break type. A
/// `ControlFlow<()>`-fixed sub-trait could be erased if needed (deferred).
pub trait Visit<Input> {
    /// The type of token group yielded.
    type Item;
    /// Visit every token group, or stop early with `ControlFlow::Break`.
    ///
    /// `&mut self`: visitors may keep scratch state (buffers, interners,
    /// automata) across items. Parallel visitation uses per-worker
    /// instances — the `ignore` crate's parallel-walker builder pattern —
    /// rather than a shared `&self`, so the stronger receiver costs the
    /// concurrent case nothing.
    fn visit<R>(
        &mut self,
        input: Input,
        f: &mut impl FnMut(Self::Item) -> ControlFlow<R>,
    ) -> ControlFlow<R>;

    /// Infallible comfort wrapper over [`Visit::visit`].
    fn for_each(&mut self, input: Input, mut f: impl FnMut(Self::Item)) {
        let _ = self.visit(input, &mut |t| {
            f(t);
            ControlFlow::<()>::Continue(())
        });
    }

    /// Concatenate with another visitor over the same input — build
    /// [`Chain`] (`self`'s items tagged `Left`, then `other`'s tagged
    /// `Right`).
    fn chain<B>(self, other: B) -> Chain<Self, B>
    where
        Self: Sized,
    {
        Chain(self, other)
    }
}

/// Sliding windows of width `N` — a demonstrative visitor source. ZST
/// leaf; `N` is compile-time.
/// Sliding `[T; N]` windows — the semantics (and name) of nightly std's
/// `slice::array_windows`; the n-gram of the featurization world.
pub struct ArrayWindows<const N: usize>;

impl<'a, T: Clone, const N: usize> Visit<&'a [T]> for ArrayWindows<N> {
    type Item = [T; N];
    fn visit<R>(
        &mut self,
        input: &'a [T],
        f: &mut impl FnMut([T; N]) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        for w in input.windows(N) {
            let arr: [T; N] = core::array::from_fn(|k| w[k].clone());
            match f(arr) {
                ControlFlow::Continue(()) => {}
                br => return br,
            }
        }
        ControlFlow::Continue(())
    }
}

/// Concatenation of two visitors over a **shared borrowed input** — the
/// fanout that *is* legal in the final encoding, because the diagonal on
/// `&Input` is free (shared references are `Copy`; visitors only read).
/// Sum-typed output stream, A's items then B's — the shape of
/// `iter::Chain`, tagged.
#[must_use = "a visitor does nothing until driven"]
pub struct Chain<A, B>(A, B);

/// Tagged item of [`Chain`] — a sum, `Left`/`Right` per the
/// `either`-crate convention.
pub enum Chained<X, Y> {
    /// An item from the first visitor.
    Left(X),
    /// An item from the second visitor.
    Right(Y),
}

impl<'i, In: ?Sized, A, B> Visit<&'i In> for Chain<A, B>
where
    A: Visit<&'i In>,
    B: Visit<&'i In>,
{
    type Item = Chained<A::Item, B::Item>;
    fn visit<R>(
        &mut self,
        input: &'i In,
        f: &mut impl FnMut(Self::Item) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        match self.0.visit(input, &mut |x| f(Chained::Left(x))) {
            ControlFlow::Continue(()) => {}
            br => return br,
        }
        self.1.visit(input, &mut |y| f(Chained::Right(y)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, string::String, vec, vec::Vec};

    #[test]
    fn graded_fmap() {
        // FnOnce grade: closure consumes a capture — impossible under a
        // uniform `Fn` bound.
        let owned = String::from("moved");
        let out = Some(1).fmap_once(move |n| format!("{n}:{owned}"));
        assert_eq!(out.unwrap(), "1:moved");
        // FnMut grade: stateful map.
        let mut acc = 0;
        assert_eq!(
            vec![1, 2, 3].fmap(|x| {
                acc += x;
                acc
            }),
            vec![1, 3, 6]
        );
    }

    #[test]
    fn grade_subsumption_supertrait() {
        fn doubles<T: MapMut<i32>>(t: T) -> T::Output<i32> {
            t.fmap(|x| x * 2)
        }
        // Vec: manual MapMut impl; Option/Result: via the blanket.
        assert_eq!(doubles(vec![1, 2]), vec![2, 4]);
        assert_eq!(doubles(Some(3)), Some(6));
        assert_eq!(doubles(Ok::<_, ()>(4)), Ok(8));
    }

    #[test]
    fn inplace_law() {
        let mut a = vec![1u64, 2, 3];
        let b = a.clone().fmap(|x| x * 10);
        map_in_place(&mut a, |x| *x *= 10);
        assert_eq!(a, b);
    }

    /// CANARY, not a law: failure on a future toolchain is information
    /// (std's in-place specialization changed), not a bug in this crate.
    #[test]
    fn inplace_reuse_canary() {
        let v: Vec<u64> = (0..1000).collect();
        let p0 = v.as_ptr() as usize;
        let w = v.fmap(|x| x + 1);
        assert_eq!(p0, w.as_ptr() as usize);
    }

    #[test]
    fn zip_associativity_and_bounds() {
        struct NoClone(u32);
        // non-Clone through Option and ZipVec: single-slot / element-wise
        // need no diagonal.
        let x = Some(NoClone(1)).zip(Some(NoClone(2)));
        assert!(matches!(x, Some((NoClone(1), NoClone(2)))));
        let z = ZipVec(vec![NoClone(7)]).zip(ZipVec(vec![NoClone(9)]));
        assert_eq!(z.0[0].1 .0, 9);

        // cartesian: associativity up to reassoc
        let (a, b, c) = (vec![1, 2], vec!["x", "y"], vec![true]);
        let lhs: Vec<_> = a
            .clone()
            .zip(b.clone())
            .zip(c.clone())
            .into_iter()
            .map(|((p, q), r)| (p, (q, r)))
            .collect();
        assert_eq!(lhs, a.zip(b.zip(c)));
    }

    #[test]
    fn array_functor_and_total_zip() {
        assert_eq!([1, 2, 3].fmap(|x| x * 10), [10, 20, 30]);
        // total zip: no truncation, length fixed by type
        assert_eq!([1, 2].zip(["a", "b"]), [(1, "a"), (2, "b")]);
    }

    #[test]
    fn pointed_units() {
        use super::Pointed;
        assert_eq!(<Option<i32> as Pointed<i32>>::pure(5), Some(5));
        assert_eq!(<Vec<i32> as Pointed<i32>>::pure(5), vec![5]);
        // and the unit law: zip(pure(()), fa) is fa up to reassoc
        let fa = Some(9);
        assert_eq!(Some(()).zip(fa).map(|((), a)| a), fa);
    }

    #[test]
    fn accumulate_is_the_seam() {
        // one pass, two algebras (featurize_x2's shape, lawful):
        use crate::base::{Count, Pair};
        let data = [1u8, 2, 3, 4];
        let Pair(grams, n): Pair<Vec<[u8; 2]>, Count> =
            accumulate(&mut ArrayWindows::<2>, &data[..]);
        assert_eq!(grams, vec![[1, 2], [2, 3], [3, 4]]);
        assert_eq!(n, Count(3));
    }

    #[test]
    fn visitor_early_exit_and_fanout() {
        // find-first without featurizing the world:
        let data = [1u8, 2, 3, 4, 5];
        let found = ArrayWindows::<2>.visit(&data[..], &mut |w: [u8; 2]| {
            if w[0] + w[1] == 7 {
                ControlFlow::Break(w)
            } else {
                ControlFlow::Continue(())
            }
        });
        assert_eq!(found, ControlFlow::Break([3, 4]));

        // concat-shaped fanout over shared input (the legal final-side one):
        let mut both = Chain(ArrayWindows::<2>, ArrayWindows::<3>);
        let mut n = 0;
        both.for_each(&data[..], |_| n += 1);
        assert_eq!(n, 4 + 3);
    }
}
