//! # `base` — the shared kernel
//!
//! Everything both spines (`data`, `machines`) import: the duplication
//! structure, the independence contract, the free pipeline morphisms, and
//! lenses-by-reborrow. Module path is permanent API; contents grow by
//! addition only.

extern crate alloc;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

// ============================== Comonoid ==============================

/// Lawful duplication: the diagonal `A -> (A, A)` of Rust's affine world.
///
/// Rust's types form (approximately) a symmetric monoidal category with
/// weakening for free (any value may be dropped) and **no free contraction**.
/// `Comonoid` is contraction, named: a signature bounding `A: Comonoid`
/// claims "this algorithm needs the diagonal", not "this type is cheap".
///
/// # Laws
/// ```
/// use affine_cat::base::Comonoid;
/// let x = String::from("witness");
/// // counit (left): drop one copy, the other equals the original
/// let (a, b) = x.clone().dup();
/// drop(a);
/// assert_eq!(b, x);
/// // counit (right)
/// let (a, b) = x.clone().dup();
/// drop(b);
/// assert_eq!(a, x);
/// ```
///
/// Equality in these laws is **value equality** (`==`), not pointer
/// identity; see [`crate::data::map_in_place`] for where the crate uses
/// pointer identity instead, and note that the two notions are kept
/// deliberately distinct.
///
/// # Foreclosed: per-type impls instead of the blanket
/// An earlier revision dropped the blanket to enable custom structural
/// rules (`Vec<B>: Comonoid ⇐ B: Comonoid`). Re-audit reversed this: the
/// motivating failure was an ownership-structure bug fixable under either
/// branch (std already propagates `Clone` structurally), and the counit
/// laws force each half of a lawful `dup` to equal the original — so the
/// population of lawful comonoids that are not lawful clones is
/// approximately empty. The blanket buys zero per-signature friction and
/// zero orphan-wall coupling; what it genuinely forecloses (excluding
/// *entangled* duplication like `Rc`) is recovered by [`Unaliased`].
/// Note the door swings one way: the blanket can never be removed
/// (semver), and structural custom-comonoid impls can never be added
/// beside it. Priced and accepted.
///
/// # Not every `Comonoid` is safe to fan out
/// Raw pointers and `Rc`/`Arc` are `Comonoid` (they are `Clone`) but their
/// duplication is *aliased* — see [`Unaliased`], which is the contract
/// [`DuplicateTo`] actually requires. `Comonoid` is "can be duplicated";
/// `Unaliased` is "duplicated independently".
///
/// # Out of scope: `Pin<P>`
/// Pinned pointers get no functor/machine impls: `fmap` consumes `self`
/// and passes the inner value to a closure *by value*, which moves the
/// pointee — precisely what `Pin` forbids. A machine over pinned state
/// needs `Pin<&mut Self>` stepping (the reason `Future::poll` has its
/// signature); that is the deferred async-machine design, not a leaf impl.
///
/// # Future directions
/// * `nightly` feature using `min_specialization` to let types override
///   `dup` for performance while the blanket provides the default —
///   exactly the tension RFC 1210's motivation describes.
pub trait Comonoid: Sized {
    /// Comultiplication. The counit is implicit: dropping is free (affine).
    fn dup(self) -> (Self, Self);
}

impl<T: Clone> Comonoid for T {
    fn dup(self) -> (Self, Self) {
        let copy = self.clone();
        (copy, self)
    }
}

// ================================ Unaliased ================================

/// **Independent** (unaliased) duplication: `dup`'s two halves never observe each
/// other. The strong diagonal.
///
/// `Clone` (hence [`Comonoid`]) permits *entangled* duplication — `Rc`,
/// `Arc`, any shared-handle type where mutation through one half is
/// visible through the other. `Unaliased` excludes it. This is the contract
/// [`DuplicateTo`] requires so that "run both branches on a copy" means what
/// it says.
///
/// # Law
/// After `let (a, b) = x.dup()`, no operation on `a` (including through
/// interior mutability) changes any observation of `b`, and vice versa.
///
/// # Safety and mechanism (foreclosed alternatives)
/// * **`unsafe trait` (Send/Sync-style)** — rejected: violating `Unaliased`
///   cannot cause UB. Thread-crossing UB is already policed by `Send`
///   (entangled `Rc` cannot cross threads at all); `Unaliased`'s residual
///   content is exactly the Send-but-entangled types (`Arc<Mutex<T>>`),
///   a *laws* matter. Precedent: `Ord`, which `BTreeMap` trusts unsafely
///   never.
/// * **Blanket over `Clone`** — rejected: would readmit the entangled
///   types, which is this trait's entire content.
/// * **Impls for `&T`** — foreclosed *by the language*: `&T: Unaliased`
///   holds iff `T` has no shared interior mutability, which is the
///   private `Freeze` trait, not nameable on stable. Conservative
///   exclusion; revisit if `Freeze` is ever exposed.
///
/// # Future directions
/// * `#[derive(Unaliased)]` checking all fields are `Unaliased`.
/// * Relaxation escape: per RFC 1105, *loosening* a bound from `Unaliased`
///   to `Comonoid` on any combinator is a non-breaking change. That
///   asymmetry is why [`DuplicateTo`] starts strict.
///
/// (Terminology: the *independent comonoid* contract — duplication whose
/// halves share no observable state, i.e. produce no aliasing.)
pub trait Unaliased: Comonoid {}

macro_rules! unaliased_leaf {
    ($($t:ty),* $(,)?) => { $(impl Unaliased for $t {})* };
}
unaliased_leaf!(
    (),
    bool,
    char,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    f32,
    f64,
    String,
    core::num::NonZeroU8,
    core::num::NonZeroU16,
    core::num::NonZeroU32,
    core::num::NonZeroU64,
    core::num::NonZeroUsize,
    core::num::NonZeroI8,
    core::num::NonZeroI16,
    core::num::NonZeroI32,
    core::num::NonZeroI64,
    core::num::NonZeroIsize
);

// IP address types live in `std` on this MSRV (core::net stabilized later).
#[cfg(feature = "std")]
unaliased_leaf!(std::net::Ipv4Addr, std::net::Ipv6Addr, std::net::IpAddr);

// Structural rules. The `+ Clone` is nominal necessity, not extra
// semantics: `Unaliased: Comonoid` and the blanket derives `Comonoid` *from*
// `Clone`, a direction the solver cannot reverse — the same nominal-Clone
// fact the cartesian `Zip` bound documents.
impl<T: Unaliased + Clone> Unaliased for Option<T> {}
impl<T: Unaliased + Clone, E: Unaliased + Clone> Unaliased for Result<T, E> {}
impl<T: Unaliased + Clone> Unaliased for Vec<T> {}
impl<T: Unaliased + Clone> Unaliased for Box<T> {}
impl<A: Unaliased + Clone, B: Unaliased + Clone> Unaliased for (A, B) {}
impl<A: Unaliased + Clone, B: Unaliased + Clone, C: Unaliased + Clone> Unaliased for (A, B, C) {}
impl<T: Unaliased + Clone, const N: usize> Unaliased for [T; N] {}
impl Unaliased for core::time::Duration {}
impl<T> Unaliased for core::marker::PhantomData<T> {}
impl<A: Unaliased + Clone, B: Unaliased + Clone, C: Unaliased + Clone, D: Unaliased + Clone>
    Unaliased for (A, B, C, D)
{
}
impl<A: Unaliased + Clone> Unaliased for core::num::Wrapping<A> {}
impl<A: Unaliased + Clone> Unaliased for core::cmp::Reverse<A> {}
impl<A: Unaliased + Clone> Unaliased for alloc::collections::VecDeque<A> {}

// ============================ Pipeline layer ============================
// Arrows as *types*: the free structure over `Piece` leaves. Category and
// monoidal laws hold definitionally — the composite's behavior is defined
// from the parts, so there is nothing left to test above the leaves.
// Monomorphization is the interpretation functor, run at compile time;
// pipelines of non-capturing leaves are zero-sized.
//
// Foreclosed (each was built and witnessed before rejection):
// * Uniform boxed hom-set (`Box<dyn Fun>` behind a GAT) — the generic
//   tower's cost is boxing at every `arr`; pruned as dead weight once the
//   monoidal presentation removed its last client. Boxing may return as
//   an explicit opt-in module, honestly priced (it is also exactly where
//   ArrowApply/Monad power lives: closures as *inhabitants*).
// * RPITIT homs — compile and compose (witnessed), but are unnameable
//   (E0562: cannot be stored in struct fields on stable) and leak auto
//   traits through unchanged signatures (a silent breaking change, per
//   RFC 1522's own drawbacks section). Permitted at construction rims,
//   never as the foundation. Reopens if TAIT/ATPIT stabilizes.
// * Hiding the combinator *types* behind abstraction — rejected:
//   `Link<F, G>` is the syntax of the free category and must stay
//   nameable so pipelines can be stored in fields (the RPITIT rejection
//   above is exactly the cost of losing the name). Representation is a
//   *separate* decision, and the `Iterator` adapter precedent cuts the
//   other way on it: `Map`'s fields are `pub(crate)`, its constructor
//   `pub(in crate::iter)`, and `.map()` is the only public door.
//   Followed here: nameable types, private fields, trait methods as the
//   sole constructors. Two decisions, two answers, one precedent.

/// A **`Piece`** — a morphism of the affine pipeline category. Objects are
/// Rust types; a `Piece<A, Out = B>` is an arrow `A -> B`; [`Link`] is
/// composition and [`Id`] the identity, and the combinators below are the
/// free structure over that category. The category is *affine symmetric
/// monoidal with a cocartesian sum*: the tensor `(A, B)` has free weakening
/// (drop, via [`KeepLeft`]/[`KeepRight`]) but a *gated* diagonal (copy, via
/// [`DuplicateTo`], bounded on [`Comonoid`]/[`Unaliased`]), while the sum
/// `Result<A, B>` is a genuine coproduct (free injections [`InjectOk`]/
/// [`InjectErr`], free case-analysis [`ConsumeResult`]).
/// **Object-safe** with the associated type fixed:
/// `&dyn Piece<A, Out = B>` works, enabling runtime-dynamic pipelines.
///
/// Grade note: reusable, grade-`Fn` (the pipeline itself may be run many
/// times). A call-once pipeline tower (`FnOnce` leaves) is a planned
/// graded extension — additive.
pub trait Piece<A> {
    /// The morphism's result type.
    type Out;
    /// Apply the morphism.
    fn run(&self, a: A) -> Self::Out;

    // --- Provided combinator methods (the `Iterator` form: on the trait
    // itself, each `where Self: Sized` so `dyn Piece` stays object-safe;
    // std merged its `IteratorExt` the same way pre-1.0). Building is
    // lazy — nothing runs until `run`. ---

    /// Composition `g ∘ f`: build [`Link`]. See its docs.
    fn link<G: Piece<Self::Out>>(self, g: G) -> Link<Self, G>
    where
        Self: Sized,
    {
        Link(self, g)
    }
    /// The **diagonal** `⟨self, g⟩` — build [`DuplicateTo`]. Copies the input, so
    /// it needs `A: Unaliased` at the point of use.
    fn duplicate_to<G: Piece<A>>(self, g: G) -> DuplicateTo<Self, G>
    where
        Self: Sized,
    {
        DuplicateTo(self, g)
    }
    /// Kleisli `>=>` on `Ok` — build [`LinkOk`].
    fn link_ok<G>(self, g: G) -> LinkOk<Self, G>
    where
        Self: Sized,
    {
        LinkOk(self, g)
    }
    /// Kleisli on `Err` (recovery) — build [`LinkErr`].
    fn link_err<G>(self, g: G) -> LinkErr<Self, G>
    where
        Self: Sized,
    {
        LinkErr(self, g)
    }
    /// Map the `Ok` arm — build [`MapOk`].
    fn map_ok(self) -> MapOk<Self>
    where
        Self: Sized,
    {
        MapOk(self)
    }
    /// Map the `Err` arm — build [`MapErr`].
    fn map_err(self) -> MapErr<Self>
    where
        Self: Sized,
    {
        MapErr(self)
    }
    /// Act on the **first** tensor component — build [`OnFirst`]. The
    /// passenger type binds at the use site (the composite is a
    /// `Piece<(A, C)>`), so no annotation is needed here.
    fn on_first(self) -> OnFirst<Self>
    where
        Self: Sized,
    {
        OnFirst(self)
    }
    /// Act on the **second** tensor component — build [`OnSecond`].
    fn on_second(self) -> OnSecond<Self>
    where
        Self: Sized,
    {
        OnSecond(self)
    }
    /// The **monoidal tensor** `self ⊗ g` — build [`Alongside`]. Also a
    /// free function ([`alongside`]); the `std::iter::zip` precedent —
    /// both doors, same combinator.
    fn alongside<C, G: Piece<C>>(self, g: G) -> Alongside<Self, G>
    where
        Self: Sized,
    {
        Alongside(self, g)
    }
    /// The **copairing** `[self, g]` — build [`ConsumeResult`]. Also a
    /// free function ([`consume_result`]); both doors, same combinator.
    fn consume_result<B, G: Piece<B, Out = Self::Out>>(self, g: G) -> ConsumeResult<Self, G>
    where
        Self: Sized,
    {
        ConsumeResult(self, g)
    }
}

/// The **monoidal tensor** `f ⊗ g` on a pair — build [`Alongside`]. Free
/// (separate inputs; see its docs). Ships as both this free function and
/// the [`Piece::alongside`] method — the `std::iter::zip` precedent: for a
/// symmetric operation the free form reads without privileging either arm,
/// the method form chains. Same combinator through either door.
/// (Foreclosed rationale: "free because the input type is a pair, not
/// `self`'s input" — [`MapOk`] is a method with exactly that property,
/// so the criterion never discriminated; demand and symmetry are the
/// real sorters.)
pub fn alongside<A, C, F: Piece<A>, G: Piece<C>>(f: F, g: G) -> Alongside<F, G> {
    Alongside(f, g)
}

/// **Copairing** `[f, g]` — build [`ConsumeResult`]. Free elimination of a
/// `Result` (see its docs). Both doors, like [`alongside`]: this free form
/// for the symmetric reading, [`Piece::consume_result`] for chains.
pub fn consume_result<A, B, C, F: Piece<A, Out = C>, G: Piece<B, Out = C>>(
    f: F,
    g: G,
) -> ConsumeResult<F, G> {
    ConsumeResult(f, g)
}

/// **Embed** a Rust function into the category: the (faithful) functor from
/// plain `Fn(A) -> B` to `Piece<A, Out = B>`, turning a closure into a
/// composable arrow. The newtype exists because a blanket
/// `impl<F: Fn(A) -> B> Piece<A> for F` would collide under coherence with
/// every named combinator type below.
#[derive(Clone, Copy, Default)]
pub struct Embed<F>(pub F);
// std's `Map` pattern: `Debug` without an `F: Debug` bound, closure
// omitted — this is what makes whole pipelines of closures debuggable
// through the combinators' derived impls.
impl<F> core::fmt::Debug for Embed<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Embed").finish_non_exhaustive()
    }
}
impl<A, B, F: Fn(A) -> B> Piece<A> for Embed<F> {
    type Out = B;
    fn run(&self, a: A) -> B {
        (self.0)(a)
    }
}

/// A shared reference to a morphism is a morphism — compose without moving.
impl<A, M: Piece<A>> Piece<A> for &M {
    type Out = M::Out;
    fn run(&self, a: A) -> M::Out {
        (*self).run(a)
    }
}

/// The identity morphism `A -> A` — the unit of [`Link`]. With it, `Piece`
/// leaves and combinators form a genuine category.
///
/// ```
/// use affine_cat::base::{Id, Embed, Piece};
/// let f = |x: i32| x + 1;
/// assert_eq!(Id.link(Embed(f)).run(10), Embed(f).run(10)); // left identity
/// assert_eq!(Embed(f).link(Id).run(10), Embed(f).run(10)); // right identity
/// ```
#[derive(Debug, Clone, Copy, Default)]
pub struct Id;
impl<A> Piece<A> for Id {
    type Out = A;
    fn run(&self, a: A) -> A {
        a
    }
}

/// Composition of the category: `self.link(g)` is `g ∘ f` written in data
/// order — run `self`, then feed its output to `g` (Control.Arrow's `>>>`).
/// Associativity and the [`Id`] identity laws are definitional (the
/// free-category laws).
///
/// Representation is private; the trait surface is the only door — and
/// that claim carries its own compile-time witness:
/// ```compile_fail,E0616
/// use affine_cat::base::{Embed, Piece};
/// let l = Embed(|x: i32| x + 1).link(Embed(|x: i32| x * 2));
/// let _inner = l.0; // error[E0616]: field `0` is private
/// ```
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Link<F, G>(F, G);
impl<A, F: Piece<A>, G: Piece<F::Out>> Piece<A> for Link<F, G> {
    type Out = G::Out;
    fn run(&self, a: A) -> G::Out {
        self.1.run(self.0.run(a))
    }
}

/// Apply a morphism to the first **product** component; the other rides
/// along untouched — Control.Arrow's `first`, the *strength* of the tensor.
///
/// Naming families: [`OnFirst`]/[`OnSecond`] act on tensor (`×`)
/// components (Strong); [`MapOk`]/[`MapErr`] act on coproduct (`+`) branches
/// (Choice), and [`Swap`] is the braiding. The distinction is
/// load-bearing — Strong needs the diagonal for its fanout, Choice never
/// does.
///
/// Bound note: this combinator needs only weakening and exchange, so
/// **no duplication bound at all** — the bounds on each combinator are
/// exactly its categorical requirements.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct OnFirst<F>(F);
impl<A, C, F: Piece<A>> Piece<(A, C)> for OnFirst<F> {
    type Out = (F::Out, C);
    fn run(&self, (a, c): (A, C)) -> Self::Out {
        (self.0.run(a), c)
    }
}

/// The **diagonal** `⟨f, g⟩` (Arrow's `&&&`): run *both* `f` and `g` on the
/// *same* input, returning `(f(a), g(a))`. This is the universal map into the
/// product, and it is the one combinator that **copies** its input — so it is
/// **gated on [`Comonoid`]/[`Unaliased`]**, the crate's affine core: in a
/// merely affine category the diagonal `Δ ⊣ ×` is *conditional*, unlike the
/// unconditional codiagonal (see [`ConsumeResult`]). Satisfies the product
/// beta laws `KeepLeft ∘ ⟨f,g⟩ = f` and `KeepRight ∘ ⟨f,g⟩ = g`.
///
/// # Law
/// The two arms are **independent**: neither observes the other's
/// execution. This is a theorem here, not a doc-hope, because the input
/// bound is [`Unaliased`] — the strong diagonal.
///
/// ```
/// use affine_cat::base::{Embed, Piece};
/// // (len &&& uppercase) >>> combine, on a String (which is Unaliased)
/// let p = Embed(|s: String| s.len())
///     .duplicate_to(Embed(|s: String| s.to_uppercase()))
///     .link(Embed(|(n, s): (usize, String)| format!("{s}/{n}")));
/// assert_eq!(p.run("dia".into()), "DIA/3");
/// // DuplicateTo is a zero-sized type: the whole pipeline compiles to nothing.
/// assert_eq!(core::mem::size_of_val(&p), 0);
/// ```
///
/// # Foreclosed: the permissive bound (`A: Comonoid`)
/// Would admit `Arc<Mutex<T>>` and friends, whose "parallel" arms are
/// entangled through the shared handle — the law above would silently
/// fail. Rejected for now on the RFC 1105 asymmetry: relaxing
/// `Unaliased -> Comonoid` later is non-breaking; tightening is not. If
/// shared-handle fanout turns out to be wanted, the escape is one
/// widening edit away (or an additional `FanoutShared` combinator).
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct DuplicateTo<F, G>(F, G);
impl<A: Unaliased, F: Piece<A>, G: Piece<A>> Piece<A> for DuplicateTo<F, G> {
    type Out = (F::Out, G::Out);
    fn run(&self, a: A) -> Self::Out {
        let (a1, a2) = a.dup();
        (self.0.run(a1), self.1.run(a2))
    }
}

/// ArrowChoice's `left` at the pipeline grade: apply on `Ok`, pass `Err`
/// through. Additive structure needs no duplication bound — the coproduct
/// adjunction `+ ⊣ Δ` is unconditional in an affine category (weakening
/// only), the mirror of [`DuplicateTo`]'s conditional `Δ ⊣ ×`.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct MapOk<F>(F);
impl<A, E, F: Piece<A>> Piece<Result<A, E>> for MapOk<F> {
    type Out = Result<F::Out, E>;
    fn run(&self, r: Result<A, E>) -> Self::Out {
        r.map(|a| self.0.run(a))
    }
}

/// **Kleisli composition in the `Result` monad** — `f >=> g`. Run `f`, and
/// on `Ok` feed the *unwrapped* value to `g`; either stage's `Err`
/// short-circuits the shared error channel. This is [`Link`] lifted to
/// fallible arrows: where `Link` composes `A -> B` with `B -> C`, `LinkOk`
/// composes `A -> Result<B, E>` with `B -> Result<C, E>`, doing the unwrap
/// and Err-bypass. Fixed to `Result` on purpose — like std's
/// `Result::and_then` it needs no monad abstraction, so it dodges the no-HKT
/// wall. The dual, chaining on the `Err` arm, is [`LinkErr`] (std `or_else`).
///
/// The hand-rolled equivalent is `Link(f, Link(MapOk(g), flatten))`.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct LinkOk<F, G>(F, G);

impl<A, B, C, E, F, G> Piece<A> for LinkOk<F, G>
where
    F: Piece<A, Out = Result<B, E>>,
    G: Piece<B, Out = Result<C, E>>,
{
    type Out = Result<C, E>;
    fn run(&self, a: A) -> Result<C, E> {
        match self.0.run(a) {
            Ok(b) => self.1.run(b),
            Err(e) => Err(e),
        }
    }
}

/// **Kleisli composition on the `Err` arm** — the dual of [`LinkOk`], std's
/// `Result::or_else`. Run `f`; on `Ok` pass the value straight through, on
/// `Err` feed the error to `g`, which may recover (`Ok`) or fail anew
/// (`Err`). Where [`LinkOk`] chains successes and short-circuits failures,
/// `LinkErr` chains failures (recovery) and short-circuits successes — the
/// same arrow with the two arms swapped.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct LinkErr<F, G>(F, G);

impl<A, B, E, X, F, G> Piece<A> for LinkErr<F, G>
where
    F: Piece<A, Out = Result<B, E>>,
    G: Piece<E, Out = Result<B, X>>,
{
    type Out = Result<B, X>;
    fn run(&self, a: A) -> Result<B, X> {
        match self.0.run(a) {
            Ok(b) => Ok(b),
            Err(e) => self.1.run(e),
        }
    }
}

/// The **copairing** `[f, g]` (Arrow's `|||`): the coproduct's *universal map
/// out* — its eliminator. Given `f : A -> C` and `g : B -> C`, consume a
/// `Result<A, B>` by case-analysis into one `C`; exactly one arm runs. The
/// codiagonal `∇ : A + A -> A` is the special case, and — dual to [`DuplicateTo`]'s
/// diagonal — it is **unconditional** in an affine category (no [`Comonoid`]
/// bound): a `match` *moves* the value into one branch, copying nothing. This
/// free-elimination / gated-diagonal asymmetry is exactly what *affine* means.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct ConsumeResult<F, G>(F, G);
impl<A, B, C, F: Piece<A, Out = C>, G: Piece<B, Out = C>> Piece<Result<A, B>>
    for ConsumeResult<F, G>
{
    type Out = C;
    fn run(&self, r: Result<A, B>) -> C {
        match r {
            Ok(a) => self.0.run(a),
            Err(b) => self.1.run(b),
        }
    }
}

/// Apply a morphism to the second product component (Strong, mirror of
/// [`OnFirst`]). No bounds: weakening and exchange only.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct OnSecond<F>(F);
impl<A, C, F: Piece<A>> Piece<(C, A)> for OnSecond<F> {
    type Out = (C, F::Out);
    fn run(&self, (c, a): (C, A)) -> Self::Out {
        (c, self.0.run(a))
    }
}

/// Apply a morphism to the `Err` branch (Choice, mirror of [`MapOk`]).
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct MapErr<F>(F);
impl<A, E, F: Piece<E>> Piece<Result<A, E>> for MapErr<F> {
    type Out = Result<A, F::Out>;
    fn run(&self, r: Result<A, E>) -> Self::Out {
        r.map_err(|e| self.0.run(e))
    }
}

/// The symmetry (braiding) of the tensor. Completes the symmetric
/// monoidal structure with [`OnFirst`]/[`OnSecond`].
#[derive(Debug, Clone, Copy, Default)]
pub struct Swap;
impl<A, B> Piece<(A, B)> for Swap {
    type Out = (B, A);
    fn run(&self, (a, b): (A, B)) -> (B, A) {
        (b, a)
    }
}

/// First **product projection** `π₁ : (A, B) -> A`. **Total and free** in an
/// affine category: discarding `B` is weakening, which is unconditional.
/// Satisfies the product beta law `KeepLeft ∘ DuplicateTo(f, g) = f`.
#[derive(Debug, Clone, Copy, Default)]
pub struct KeepLeft;
impl<A, B> Piece<(A, B)> for KeepLeft {
    type Out = A;
    fn run(&self, (a, _b): (A, B)) -> A {
        a
    }
}

/// Second **product projection** `π₂ : (A, B) -> B`. Dual of [`KeepLeft`];
/// `KeepRight ∘ DuplicateTo(f, g) = g`.
#[derive(Debug, Clone, Copy, Default)]
pub struct KeepRight;
impl<A, B> Piece<(A, B)> for KeepRight {
    type Out = B;
    fn run(&self, (_a, b): (A, B)) -> B {
        b
    }
}

/// The **left coproduct injection** `ι₁ : A -> Result<A, B>`, sending a value
/// into the `Ok` arm. Free (mere tagging — injections cost nothing in an
/// affine category). Satisfies coproduct beta
/// `ConsumeResult(f, g) ∘ InjectOk = f`.
#[derive(Debug, Clone, Copy, Default)]
pub struct InjectOk<B>(core::marker::PhantomData<fn(B)>);
/// Constructor for [`InjectOk`] at error-type `B`.
pub fn inject_ok<B>() -> InjectOk<B> {
    InjectOk(core::marker::PhantomData)
}
impl<A, B> Piece<A> for InjectOk<B> {
    type Out = Result<A, B>;
    fn run(&self, a: A) -> Result<A, B> {
        Ok(a)
    }
}

/// The **right coproduct injection** `ι₂ : B -> Result<A, B>`, sending a value
/// into the `Err` arm. Dual of [`InjectOk`];
/// `ConsumeResult(f, g) ∘ InjectErr = g`.
#[derive(Debug, Clone, Copy, Default)]
pub struct InjectErr<A>(core::marker::PhantomData<fn(A)>);
/// Constructor for [`InjectErr`] at ok-type `A`.
pub fn inject_err<A>() -> InjectErr<A> {
    InjectErr(core::marker::PhantomData)
}
impl<A, B> Piece<B> for InjectErr<A> {
    type Out = Result<A, B>;
    fn run(&self, b: B) -> Result<A, B> {
        Err(b)
    }
}

/// The **monoidal tensor** `f ⊗ g` (the product bifunctor's action, Arrow's
/// `***`): apply `f` to the first component and `g` to the second,
/// `(A, C) -> (f(A), g(C))`. The two arms act on *different* inputs — the
/// two halves of the pair — so nothing is copied and no [`Comonoid`] bound
/// is needed: the tuple is destructured, each half moved into one arm.
/// Equals `Link(OnFirst(f), OnSecond(g))`.
#[must_use = "pieces are lazy and do nothing unless `run`"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Alongside<F, G>(F, G);
impl<A, C, F: Piece<A>, G: Piece<C>> Piece<(A, C)> for Alongside<F, G> {
    type Out = (F::Out, G::Out);
    fn run(&self, (a, c): (A, C)) -> Self::Out {
        (self.0.run(a), self.1.run(c))
    }
}

// ================================ Absorb ================================

/// A consumer/sink: the algebra side of the free–forgetful adjunction.
///
/// `Vec<A>` is the free monoid on `A`; the adjunction's universal property
/// says a structure-map out of it is determined by what happens to one
/// element — which is exactly this trait. `absorb` is the algebra action;
/// there is no `finish`: in affine style the caller owns the accumulator
/// and simply keeps it (`core::hash::Hasher`'s `write`, and the
/// `Accumulates` trait of creature_feature, are this shape).
///
/// This is the crate's cross-spine seam: a [`crate::machines::Machine`] is
/// an `Absorb` plus a readout; an `Absorb` is a machine that keeps its
/// counsel. Accordingly the trait lives in the kernel and each spine owns
/// its instances.
///
/// # Law
/// Order-respecting fold: absorbing `t1` then `t2` is the composite
/// algebra action — no reordering, no dropping. (Commutative absorbers may
/// additionally document commutativity; that stronger law is what licenses
/// parallel accumulation.)
#[must_use = "an Absorb sink accumulates nothing until it is fed; construct-and-drop is almost certainly a bug"]
/// **Object-safe**: `&mut dyn Absorb<T>` works — heterogeneous sinks behind
/// a trait object are fine, since `absorb` has no generic parameters.
pub trait Absorb<T> {
    /// Absorb one item into the accumulator.
    fn absorb(&mut self, t: T);

    /// Feed every item of `input` in order — the fold eliminator as a
    /// method (std's `for_each`/`collect` position; see also
    /// [`crate::data::accumulate`], which additionally hands back a
    /// finished value). `where Self: Sized` keeps it off the vtable, so
    /// `&mut dyn Absorb<T>` object-safety is unchanged.
    fn accumulate<I: IntoIterator<Item = T>>(&mut self, input: I)
    where
        Self: Sized,
    {
        for t in input {
            self.absorb(t);
        }
    }
}

// Std collection instances. Deliberately NOT a blanket over `Extend`:
// `Extend<T>` carries a type parameter, so downstream crates can legally
// implement it for foreign types (uncovered local type in trait-parameter
// position), which makes any blanket over it conflict with every concrete
// impl — the same coherence law that shaped the `MapOnce`/`MapMut`
// architecture, met here from the std side. Blankets are viable only over
// parameter-free traits (`Iterator`); over parameterized ones they are
// coherence poison. Manual impls it is:
macro_rules! absorb_via_extend {
    ($($ty:ty { $($g:tt)* }),* $(,)?) => {$(
        impl<$($g)*> Absorb<T> for $ty {
            fn absorb(&mut self, t: T) { self.extend(core::iter::once(t)); }
        }
    )*};
}
absorb_via_extend! {
Vec<T> { T },
alloc::collections::VecDeque<T> { T },
alloc::collections::BTreeSet<T> { T: Ord },
alloc::collections::BinaryHeap<T> { T: Ord },
}
impl Absorb<char> for String {
    fn absorb(&mut self, t: char) {
        self.push(t);
    }
}
impl<'a> Absorb<&'a str> for String {
    fn absorb(&mut self, t: &'a str) {
        self.push_str(t);
    }
}
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K: core::hash::Hash + Eq, V> Absorb<(K, V)> for std::collections::HashMap<K, V> {
    fn absorb(&mut self, (k, v): (K, V)) {
        self.insert(k, v);
    }
}
impl<K: Ord, V> Absorb<(K, V)> for alloc::collections::BTreeMap<K, V> {
    fn absorb(&mut self, (k, v): (K, V)) {
        self.insert(k, v);
    }
}

/// The terminal sink: absorb anything, keep nothing. The `Absorb`
/// identity object — "traverse for effect".
impl<T> Absorb<T> for () {
    fn absorb(&mut self, _t: T) {}
}

/// Counting absorber (not `Extend`, hence a manual instance).
#[derive(Default, Debug, PartialEq, Eq)]
pub struct Count(pub usize);
impl<T> Absorb<T> for Count {
    fn absorb(&mut self, _t: T) {
        self.0 += 1;
    }
}

/// Product of algebras: absorb into two accumulators from one stream —
/// one pass, two outputs (creature_feature's `featurize_x2`, as a lawful
/// instance). The token is genuinely duplicated, so the [`Comonoid`]
/// bound sits exactly where the theory puts it.
///
/// **Fields are public on purpose** — the one deliberate exception to the
/// private-representation rule. `Absorb` is a *carrier* trait: the
/// accumulators are the result, and `let Pair(a, b) = acc` is how you
/// take them home. Opacity is right exactly when the trait's methods are
/// the whole observation (`Piece::run`, `Machine::out`); for `Absorb`
/// they are not, so the fields stay open.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct Pair<A, B>(pub A, pub B);
impl<T: Comonoid, A: Absorb<T>, B: Absorb<T>> Absorb<T> for Pair<A, B> {
    fn absorb(&mut self, t: T) {
        let (t1, t2) = t.dup();
        self.0.absorb(t1);
        self.1.absorb(t2);
    }
}

// ============================ RoundTripApprox connections ============================

/// An adjunction between posets — the fragment of adjointness whose
/// triangle identities collapse to a decidable biconditional, so the crate
/// can *test* it rather than assert it.
///
/// **Why *approx*:** neither round-trip is the identity — you return to
/// something *ordered-close*, not equal (`a <= upper(lower(a))` and
/// `lower(upper(b)) <= b`), bounded by `<=` on each side. Contrast
/// [`RoundTripExact`], whose forward leg recovers the value exactly. This is
/// the abstraction/concretization pair of abstract interpretation.
///
/// # Law
/// `lower(a) <= b`  ⟺  `a <= upper(b)` (for all `a`, `b`).
/// Corollaries (the triangle identities in poset form):
/// `a <= upper(lower(a))`, `lower(upper(b)) <= b`, and both round-trips
/// are idempotent.
pub trait RoundTripApprox<A: PartialOrd, B: PartialOrd> {
    /// Left adjoint (e.g. `align_up`, `ceil`).
    fn lower(&self, a: A) -> B;
    /// Right adjoint (e.g. `align_down`, `floor`).
    fn upper(&self, b: B) -> A;
}

/// Check the adjunction law at a point — enumerate over a domain in tests.
pub fn round_trip_approx_law<A, B, G>(g: &G, a: A, b: B) -> bool
where
    A: PartialOrd + Clone,
    B: PartialOrd + Clone,
    G: RoundTripApprox<A, B>,
{
    (g.lower(a.clone()) <= b) == (a <= g.upper(b))
}

// ============================ RoundTripExact (roundtrip) ============================

/// A RoundTripApprox insertion / split idempotent: the serde-shaped contract.
/// `de ∘ ser = id` on values; `ser ∘ de` is a *canonicalization* on
/// representations. The round-trip laws are the triangle identities of a
/// (thin) adjunction, which is why every proptest round-trip suite is
/// adjointness verification without the name.
///
/// # Laws
/// * `de(ser(t)) == Some(t)`
/// * `ser(de(r)?) ; de` agrees with `de(r)` — canonicalization is
///   invisible to decoding (idempotence on the image).
pub trait RoundTripExact<T> {
    /// The serialized representation.
    type Repr;
    /// Serialize (total).
    fn ser(&self, t: &T) -> Self::Repr;
    /// Deserialize (partial: not every representation is valid).
    fn de(&self, r: Self::Repr) -> Option<T>;
}

// ============================ Lenses by reborrow ============================

/// Compose two mutable projections. A `&mut S -> &mut A` projection **is**
/// a lens: `&*p(s)` is get, `*p(s) = v` is put, and the get-put / put-get /
/// put-put laws are theorems of the borrow system — reads and writes
/// through a unique place trivially satisfy them.
///
/// This is not folklore only: the verification line RustHorn →
/// RustHornBelt → Creusot models `&mut T` as the pair (current value,
/// final/prophesied value) — the lens presentation — and on it translates
/// Rust programs to pure functional programs. The crate's mutation story
/// rides on the same fact.
///
/// # Foreclosed: reified lens objects (get/put structs)
/// Would buy lens collections and runtime-chosen optics, at the price of
/// converting laws-by-construction back into proof obligations. The trade
/// runs the wrong way for a laws-first crate. The boxed direction remains
/// available later as an addition.
///
/// (`A: 'static` is a wart of closure lifetime inference on the returned
/// `for<'r> Fn` signature, not of the construction.)
pub fn lens<S, A: 'static, B>(
    p: impl Fn(&mut S) -> &mut A,
    q: impl Fn(&mut A) -> &mut B,
) -> impl Fn(&mut S) -> &mut B {
    move |s| q(p(s))
}

/// Re-exported for visitor signatures ([`crate::data::Visit`]).
pub use core::ops::ControlFlow;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, string::String, string::ToString, vec, vec::Vec};

    #[test]
    fn link_ok_and_link_err_are_result_kleisli() {
        // link_ok = and_then (chain Ok); link_err = or_else (chain Err).
        let parse = Embed(|s: &str| s.parse::<i64>().map_err(|_| "bad"));
        let pos = Embed(|n: i64| if n > 0 { Ok(n) } else { Err("nonpos") });
        let recover = Embed(|_e: &str| Ok::<i64, &str>(0));
        // link_ok: Ok chains onward, Err short-circuits
        let ok_chain = LinkOk(parse, pos);
        assert_eq!(ok_chain.run("7"), Ok(7));
        assert_eq!(ok_chain.run("x"), Err("bad"));
        assert_eq!(ok_chain.run("-1"), Err("nonpos"));
        // link_err: Err chains into recovery, Ok passes through
        let with_recovery = LinkErr(parse, recover);
        assert_eq!(with_recovery.run("7"), Ok(7));
        assert_eq!(with_recovery.run("x"), Ok(0)); // recovered
    }

    #[test]
    fn ext_methods_build_the_combinators() {
        // f.link(g) == Link(f, g); the method surface reads as composition.
        let f = Embed(|x: i32| x + 1);
        let g = Embed(|x: i32| x * 2);
        assert_eq!(f.link(g).run(10), Link(Embed(|x: i32| x + 1), g).run(10));
        // duplicate_to builds DuplicateTo (needs Unaliased at use — i32 is Copy)
        let both = Embed(|x: i32| x + 1).duplicate_to(Embed(|x: i32| x * 2));
        assert_eq!(both.run(10), (11, 20));
        // alongside builds the tensor on a pair
        let t = alongside(Embed(|x: i32| x + 1), Embed(|s: &str| s.len()));
        assert_eq!(t.run((10, "abc")), (11, 3));
        // consume_result eliminates a Result to one type
        let c = consume_result(Embed(|x: i32| x), Embed(|_e: &str| -1));
        assert_eq!(c.run(Ok(5)), 5);
        assert_eq!(c.run(Err("e")), -1);
    }

    #[test]
    fn pipelines_of_closures_are_debug() {
        // The std `Map` pattern's payoff: `Embed`'s manual Debug carries
        // no `F: Debug` bound, so combinator derives make whole
        // closure pipelines debuggable.
        let p = Embed(|x: i32| x + 1).link(Embed(|x: i32| x * 2));
        assert_eq!(format!("{p:?}"), "Link(Embed { .. }, Embed { .. })");
    }

    #[test]
    fn comonoid_laws() {
        let x = String::from("witness");
        let (a, b) = x.clone().dup();
        assert_eq!(a, x);
        assert_eq!(b, x);
        // coassociativity up to reassoc:
        let (p, q) = x.clone().dup();
        let (l1, l2) = p.dup();
        assert_eq!((l1, l2, q), (x.clone(), x.clone(), x));
    }

    #[test]
    fn fanout_requires_indep_and_is_zero_sized() {
        // String: Unaliased — compiles; Rc<..> would be rejected at compile time.
        let p = Link(
            DuplicateTo(
                Embed(|s: String| s.len()),
                Embed(|s: String| s.to_uppercase()),
            ),
            Embed(|(n, s): (usize, String)| format!("{s}/{n}")),
        );
        assert_eq!(p.run("dia".into()), "DIA/3");
        assert_eq!(core::mem::size_of_val(&p), 0);
    }

    #[test]
    fn product_and_coproduct_beta_laws() {
        let f = |x: i32| x + 1;
        let g = |x: i32| x * 2;
        // product beta: Fst ∘ ⟨f,g⟩ = f, Snd ∘ ⟨f,g⟩ = g
        let paired = DuplicateTo(Embed(f), Embed(g)); // ⟨f,g⟩ (i32: Unaliased)
        let (l, r) = paired.run(5);
        assert_eq!(KeepLeft.run((l, r)), f(5));
        let (l, r) = paired.run(5);
        assert_eq!(KeepRight.run((l, r)), g(5));
        // coproduct beta: [f,g] ∘ Inl = f, [f,g] ∘ Inr = g
        let case = ConsumeResult(Embed(f), Embed(g));
        assert_eq!(case.run(inject_ok::<i32>().run(5)), f(5));
        assert_eq!(case.run(inject_err::<i32>().run(5)), g(5));
        // bifunctor Alongside = OnFirst then OnSecond
        assert_eq!(Alongside(Embed(f), Embed(g)).run((10, 20)), (11, 40));
    }

    #[test]
    fn identity_laws() {
        // Link(Id, f) == f == Link(f, Id): the category unit laws
        let f = Embed(|x: i32| x + 1);
        assert_eq!(Link(Id, Embed(|x: i32| x + 1)).run(10), f.run(10));
        assert_eq!(Link(Embed(|x: i32| x + 1), Id).run(10), f.run(10));
    }

    #[test]
    fn strong_choice_completions() {
        let p = Link(Swap, OnSecond(Embed(|x: u32| x + 1)));
        assert_eq!(p.run((10u32, "k")), ("k", 11));
        let e = MapErr(Embed(|s: String| s.len()));
        assert_eq!(e.run(Ok::<u32, String>(5)), Ok(5));
        assert_eq!(e.run(Err::<u32, String>("four".into())), Err(4));
    }

    #[test]
    fn unaliased_excludes_aliased_duplication() {
        // Positive: these compile (are Unaliased).
        fn requires_unaliased<T: Unaliased>() {}
        requires_unaliased::<u32>();
        requires_unaliased::<(bool, char)>();
        requires_unaliased::<alloc::string::String>();
        // Negative instances (*mut T, Rc, &mut T) are verified by their
        // ABSENCE from any Unaliased impl; asserting non-impl in a test
        // requires nightly auto-trait tricks, so the guarantee lives in the
        // impl list + docs rather than here. This test pins the positive
        // direction so a regression that dropped a leaf would fail.
    }

    #[test]
    fn absorb_kernel() {
        // blanket via Extend, manual Count, product with the comonoid bound:
        let mut acc: Pair<Vec<u32>, Count> = Pair::default();
        for t in [3u32, 1, 4] {
            acc.absorb(t);
        }
        assert_eq!(acc, Pair(vec![3, 1, 4], Count(3)));
    }

    #[test]
    fn galois_alignment() {
        struct Align8;
        impl RoundTripApprox<usize, usize> for Align8 {
            fn lower(&self, a: usize) -> usize {
                a.div_ceil(8)
            } // up into units
            fn upper(&self, b: usize) -> usize {
                b * 8
            } // units back to bytes
        }
        for a in 0..100 {
            for b in 0..20 {
                assert!(round_trip_approx_law(&Align8, a, b), "failed at ({a},{b})");
            }
        }
    }

    #[test]
    fn retract_roundtrip() {
        struct Dec; // i32 <-> decimal string
        impl RoundTripExact<i32> for Dec {
            type Repr = String;
            fn ser(&self, t: &i32) -> String {
                t.to_string()
            }
            fn de(&self, r: String) -> Option<i32> {
                r.parse().ok()
            }
        }
        for t in [-5i32, 0, 42, i32::MAX] {
            assert_eq!(Dec.de(Dec.ser(&t)), Some(t));
        }
        // canonicalization: "+42" decodes, re-serializes canonically
        let canon = Dec.ser(&Dec.de("+42".into()).unwrap());
        assert_eq!(Dec.de(canon), Dec.de("+42".into()));
    }

    #[test]
    fn lens_by_reborrow() {
        struct Engine {
            rpm: u32,
        }
        struct Car {
            engine: Engine,
        }
        let rpm = lens(|c: &mut Car| &mut c.engine, |e: &mut Engine| &mut e.rpm);
        let mut car = Car {
            engine: Engine { rpm: 800 },
        };
        *rpm(&mut car) = 6000;
        assert_eq!(*rpm(&mut car), 6000);
    }
}
