//! The weight algebra beneath [`crate::weighted`]: a stratified hierarchy from
//! semirings up to rings, where each tier adds exactly the axiom a given
//! automaton operation requires.
//!
//! A weighted automaton reads out a *weight* rather than a mere accept/reject
//! bit; a Boolean recognizer (`Machine<Out = bool>`) is the special case
//! where the weight is [`bool`]. The operations that combine automata — union, intersection,
//! star — each need a different amount of algebraic structure on that weight
//! type, and the literature (Mohri, *Weighted Automata Algorithms*) pins the
//! requirements precisely. This module encodes that dependency structure as a
//! trait tower, so a combinator can demand exactly its tier and the compiler
//! rejects, say, a symmetric difference over a semiring with no negation.
//!
//! # `&mut`-native, with value forms for free
//! Each operation's **primitive is in-place** (`add_assign(&mut self, &Self)`)
//! and the **value form is a default method** (`add(self, &Self) -> Self`).
//! This is the crate's own [`crate::data::MapMut`] / [`crate::data::map_in_place`]
//! split, and std's `Add` / `AddAssign` split, for the same reason: a *large*
//! weight (a polynomial/power-series, a matrix, a set) wants in-place `+` to
//! avoid reallocating on every step, while the value form is what the
//! distributivity-shaped readout logic of a product automaton — and the law
//! statements — are written in. The bound is [`Clone`], not `Copy`, so large
//! non-`Copy` weights like [`Poly`] fit; scalar (`Copy`) weights pay nothing
//! for the value form.
//!
//! Identities are `fn zero()` / `fn one()` rather than `const`, because a
//! heap-backed weight cannot always have a `const` identity.
//!
//! # The tiers
//! * [`Semiring`] — `(S, +, 0)` a commutative monoid, `(S, *, 1)` a monoid,
//!   `*` distributes over `+`, and `0` annihilates `*`. Enough for **union**
//!   (`+`) and **deterministic intersection** (`*`).
//! * [`CommutativeSemiring`] — `*` also commutative. Gates **nondeterministic
//!   intersection and composition**.
//! * (removed tiers — see the note above [`Ring`]: `CompleteSemiring`
//!   and `Divisible` gated operations no combinator ships; restorable
//!   additively with the operation that needs them)
//! * [`Ring`] — `+` is a *group*: every weight has an additive inverse. Gates
//!   true **subtraction** and symmetric-difference.
//!
//! Commutativity is a *promise the impl makes*, unverifiable by the compiler
//! — the same status as [`crate::base::Unaliased`].
//!
//! # Two structures on booleans
//! [`bool`] recovers the recognizer algebra: [`crate::weighted::Sum`] is `+`
//! (`or`, union) and [`crate::weighted::Prod`] is `*` (`and`, intersection). But `bool` under `or` is **not a ring** — `or` is
//! idempotent, so no element except `false` has an additive inverse. The ring
//! structure on booleans is a *different* `+`: [`Gf2`] uses `XOR` (a group,
//! every element self-inverse) with `AND`, the two-element field. So the DFA
//! recognizer algebra silently uses **two** structures on the same bits — the
//! Boolean semiring `(or, and)` for union/intersection, and GF(2) `(xor, and)`
//! for symmetric difference — which is why symmetric difference needs a ring
//! while union does not.
//!
//! Idempotent semirings ([`bool`]-under-`or`, [`Tropical`], [`Viterbi`]) are
//! *never* rings — idempotence plus inverses forces the trivial ring — so
//! they implement the semiring tiers but not [`Ring`].

use alloc::vec::Vec;

use crate::base::Absorb;

/// Every semiring weight is an [`Absorb`] sink over itself: absorbing an item
/// folds it in with `⊕`. This makes a weight a drop-in accumulator for the
/// data spine — `crate::data::accumulate` can drive a `Visit` straight into a
/// running `⊕`-sum.
///
/// **Seed with [`Semiring::zero`]** (the `⊕`-identity), which is exactly what
/// every instance's [`Default`] returns here — including [`Tropical`], whose
/// `Default` is overridden to `zero()` (`+∞`) precisely so a `Default`-seeded
/// accumulator is correct. Feeding into a non-`zero` seed computes
/// `seed ⊕ (sum of items)`, which is only the plain sum when `seed = zero`.
impl<S: Semiring> Absorb<S> for S {
    fn absorb(&mut self, item: S) {
        self.add_assign(&item);
    }
}

/// A semiring `(S, +, *, 0, 1)`: the minimum structure for weighted automata.
/// `(S, +, zero)` is a commutative monoid, `(S, *, one)` a monoid, `*`
/// distributes over `+`, and `zero` annihilates `*`.
///
/// The in-place `add_assign`/`mul_assign` are the primitives; the value forms
/// `add`/`mul` default to them.
///
/// # Laws
/// * `+` associative, commutative, identity `zero()`.
/// * `*` associative, identity `one()`.
/// * `a * (b + c) = (a * b) + (a * c)` (and the right version).
/// * `a * zero() = zero() * a = zero()`.
pub trait Semiring: Clone + PartialEq {
    /// The additive identity `0` — also the `*` annihilator.
    fn zero() -> Self;
    /// The multiplicative identity `1`.
    fn one() -> Self;
    /// In-place `+`: `self <- self + rhs`. The primitive.
    fn add_assign(&mut self, rhs: &Self);
    /// In-place `*`: `self <- self * rhs`. The primitive.
    fn mul_assign(&mut self, rhs: &Self);

    /// `self + rhs` by value. Defaults to [`Semiring::add_assign`].
    fn add(mut self, rhs: &Self) -> Self
    where
        Self: Sized,
    {
        self.add_assign(rhs);
        self
    }
    /// `self * rhs` by value. Defaults to [`Semiring::mul_assign`].
    fn mul(mut self, rhs: &Self) -> Self
    where
        Self: Sized,
    {
        self.mul_assign(rhs);
        self
    }
}

/// A [`Semiring`] whose `*` is also commutative. A marker (no new methods):
/// an unverifiable promise, like [`crate::base::Unaliased`]. Required for
/// intersection and composition of *nondeterministic* weighted automata.
pub trait CommutativeSemiring: Semiring {}

// Removed tiers (the `dfa` convention: unbuilt machinery lives in
// comments, not surface): `CompleteSemiring` (closure `a* = Σ aⁿ`, Conway
// law `a* = 1 + a·a*`) gated a Kleene star no combinator ships, and
// `Divisible` (partial division) gated determinization/weight-pushing
// that were never built. Both are restorable ADDITIVELY the day a star or
// determinization lands (RFC 1105's asymmetry, as `base` cites); their
// instances were: star — bool (`true`), Tropical (`0`), Viterbi (`1.0`),
// Gf2 (`one`, telescoping); divide — Tropical (`checked_sub`).

/// A [`Semiring`] whose `+` is a commutative *group*: every weight has an
/// additive inverse. A ring proper (a semiring with negation). Enables
/// genuine subtraction and, over a characteristic-2 ring like [`Gf2`],
/// symmetric difference as `+`.
///
/// # Law
/// `a + neg(a) = zero()` for all `a`.
pub trait Ring: Semiring {
    /// In-place negation: `self <- -self`. The primitive.
    fn neg_assign(&mut self);

    /// `-self` by value. Defaults to [`Ring::neg_assign`].
    fn neg(mut self) -> Self
    where
        Self: Sized,
    {
        self.neg_assign();
        self
    }
    /// In-place subtraction: `self <- self - rhs`. Defaults to
    /// `self.add_assign(&rhs.neg())`.
    fn sub_assign(&mut self, rhs: &Self) {
        let neg_rhs = rhs.clone().neg();
        self.add_assign(&neg_rhs);
    }
    /// `self - rhs` by value. Defaults to [`Ring::sub_assign`].
    fn sub(mut self, rhs: &Self) -> Self
    where
        Self: Sized,
    {
        self.sub_assign(rhs);
        self
    }
}

// ---- Boolean semiring: bool with (or, and). The DFA-algebra weight. ----
impl Semiring for bool {
    fn zero() -> bool {
        false
    }
    fn one() -> bool {
        true
    }
    fn add_assign(&mut self, r: &bool) {
        *self |= *r;
    }
    fn mul_assign(&mut self, r: &bool) {
        *self &= *r;
    }
}
impl CommutativeSemiring for bool {}

// ---- Counting semiring: u64 with (+, *). NOT complete (star diverges). ----
impl Semiring for u64 {
    fn zero() -> u64 {
        0
    }
    fn one() -> u64 {
        1
    }
    fn add_assign(&mut self, r: &u64) {
        *self = self.saturating_add(*r);
    }
    fn mul_assign(&mut self, r: &u64) {
        *self = self.saturating_mul(*r);
    }
}
impl CommutativeSemiring for u64 {}

// ---- The integers as a ring: i64 with wrapping = Z/2^64 (lawful). ----
impl Semiring for i64 {
    fn zero() -> i64 {
        0
    }
    fn one() -> i64 {
        1
    }
    fn add_assign(&mut self, r: &i64) {
        *self = self.wrapping_add(*r);
    }
    fn mul_assign(&mut self, r: &i64) {
        *self = self.wrapping_mul(*r);
    }
}
impl CommutativeSemiring for i64 {}
impl Ring for i64 {
    fn neg_assign(&mut self) {
        *self = self.wrapping_neg();
    }
}

/// The **tropical** semiring `(min, +)` over `u64`, with `zero = infinity` and
/// `one = 0`. Weighted automata over it compute **shortest paths / minimum
/// cost** — `+` is the minimum of path weights, `*` their total.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tropical(pub u64);

// `Default` is the ⊕-identity (`zero()` = +∞), NOT the derived `Tropical(0)`
// (which is `one()`), so `Tropical` is a valid empty ⊕-accumulator — see the
// `Absorb` blanket below. This is the one instance where the derived default
// would disagree with `zero()`.
impl Default for Tropical {
    fn default() -> Tropical {
        Tropical::zero()
    }
}

impl Semiring for Tropical {
    fn zero() -> Tropical {
        Tropical(u64::MAX) // infinity
    }
    fn one() -> Tropical {
        Tropical(0)
    }
    fn add_assign(&mut self, r: &Tropical) {
        self.0 = self.0.min(r.0);
    }
    fn mul_assign(&mut self, r: &Tropical) {
        self.0 = self.0.saturating_add(r.0);
    }
}
impl CommutativeSemiring for Tropical {}

/// The **Viterbi** semiring `(max, *)` over `f64` probabilities in `[0, 1]`,
/// with `zero = 0.0` and `one = 1.0`. Weighted automata over it compute the
/// **most-likely path** — `+` keeps the better alternative, `*` multiplies
/// probabilities along a path.
///
/// The field is private and [`Viterbi::new`] validating — the only
/// constructor —
/// so `NaN` and out-of-range values are unrepresentable and every held
/// value satisfies the laws' precondition by construction (contrast
/// [`Tropical`], whose whole `u64` range is lawful and whose field is
/// therefore public). One caveat survives validation and is stated here
/// rather than hidden: `*` is IEEE-754 multiplication, so
/// `⊗`-**associativity holds up to rounding** (ULP-level), exactly on
/// clean dyadic values. `max` is exact.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct Viterbi(f64);

impl Viterbi {
    /// Validate a probability into the semiring: `Some` iff `p` is in
    /// `[0.0, 1.0]` (which excludes `NaN` — comparisons with `NaN` are
    /// false).
    pub fn new(p: f64) -> Option<Viterbi> {
        (0.0..=1.0).contains(&p).then_some(Viterbi(p))
    }

    /// The held probability (in `[0.0, 1.0]` by construction).
    pub fn get(self) -> f64 {
        self.0
    }
}

impl Semiring for Viterbi {
    fn zero() -> Viterbi {
        Viterbi(0.0)
    }
    fn one() -> Viterbi {
        Viterbi(1.0)
    }
    fn add_assign(&mut self, r: &Viterbi) {
        self.0 = self.0.max(r.0);
    }
    fn mul_assign(&mut self, r: &Viterbi) {
        self.0 *= r.0;
    }
}
impl CommutativeSemiring for Viterbi {}

/// **GF(2)**, the two-element field: booleans under `+ = XOR`, `* = AND`.
/// This is the *ring* structure on booleans — distinct from the Boolean
/// semiring `(or, and)` — and its `+` is exactly symmetric difference.
/// Symmetric difference of recognizers, on acceptance bits, is this ring's addition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Gf2(pub bool);

impl Semiring for Gf2 {
    fn zero() -> Gf2 {
        Gf2(false)
    }
    fn one() -> Gf2 {
        Gf2(true)
    }
    fn add_assign(&mut self, r: &Gf2) {
        self.0 ^= r.0; // XOR — the group operation
    }
    fn mul_assign(&mut self, r: &Gf2) {
        self.0 &= r.0;
    }
}
impl CommutativeSemiring for Gf2 {}
impl Ring for Gf2 {
    fn neg_assign(&mut self) {
        // characteristic 2: every element is its own inverse — a no-op.
    }
}

/// A **polynomial / formal-power-series** semiring over [`i64`]: coefficients
/// low-degree first, `+` elementwise addition, `*` convolution, `zero` the
/// empty polynomial, `one` the constant `1`. This is a *large*, heap-backed
/// weight (`Clone`, not `Copy`) — the case that motivates the `&mut`-native
/// design: [`Semiring::add_assign`] extends and adds in place, reallocating
/// only when the right operand is longer.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Poly(pub Vec<i64>);

impl Poly {
    fn trim(&mut self) {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }
}

impl Semiring for Poly {
    fn zero() -> Poly {
        Poly(Vec::new())
    }
    fn one() -> Poly {
        Poly(alloc::vec![1])
    }
    fn add_assign(&mut self, r: &Poly) {
        if r.0.len() > self.0.len() {
            self.0.resize(r.0.len(), 0);
        }
        for (a, b) in self.0.iter_mut().zip(&r.0) {
            *a = a.wrapping_add(*b);
        }
        self.trim();
    }
    fn mul_assign(&mut self, r: &Poly) {
        if self.0.is_empty() || r.0.is_empty() {
            self.0.clear();
            return;
        }
        // convolution changes the shape, so it allocates a fresh buffer.
        let mut out = alloc::vec![0i64; self.0.len() + r.0.len() - 1];
        for (i, &a) in self.0.iter().enumerate() {
            for (j, &b) in r.0.iter().enumerate() {
                out[i + j] = out[i + j].wrapping_add(a.wrapping_mul(b));
            }
        }
        self.0 = out;
        self.trim();
    }
}
impl CommutativeSemiring for Poly {}
impl Ring for Poly {
    fn neg_assign(&mut self) {
        for a in &mut self.0 {
            *a = a.wrapping_neg();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn viterbi_constructor_polices_the_domain() {
        // The [0, 1] precondition is enforced at the only constructor; NaN is
        // excluded (NaN fails every range comparison).
        assert!(Viterbi::new(0.0).is_some());
        assert!(Viterbi::new(0.5).is_some());
        assert!(Viterbi::new(1.0).is_some());
        assert!(Viterbi::new(-0.1).is_none());
        assert!(Viterbi::new(1.1).is_none());
        assert!(Viterbi::new(f64::NAN).is_none());
        assert!(Viterbi::new(f64::INFINITY).is_none());
        assert_eq!(Viterbi::new(0.25).unwrap().get(), 0.25);
    }

    fn distributes<S: Semiring>(a: S, b: S, c: S) -> bool {
        a.clone().mul(&b.clone().add(&c)) == a.clone().mul(&b).add(&a.mul(&c))
    }
    fn annihilates<S: Semiring>(a: S) -> bool {
        a.clone().mul(&S::zero()) == S::zero() && S::zero().mul(&a) == S::zero()
    }
    fn identities<S: Semiring>(a: S) -> bool {
        a.clone().add(&S::zero()) == a && a.clone().mul(&S::one()) == a
    }
    fn ring_law<S: Ring>(a: S) -> bool {
        a.clone().add(&a.clone().neg()) == S::zero() && a.clone().sub(&a) == S::zero()
    }

    #[test]
    fn semiring_laws_scalars() {
        for &a in &[false, true] {
            assert!(annihilates(a) && identities(a));
            for &b in &[false, true] {
                for &c in &[false, true] {
                    assert!(distributes(a, b, c));
                }
            }
        }
        for a in [0u64, 1, 5, 100] {
            assert!(annihilates(a) && identities(a));
            for b in [0u64, 2, 7] {
                for c in [0u64, 3, 9] {
                    assert!(distributes(a, b, c));
                }
            }
        }
        for a in [Tropical(0), Tropical(3), Tropical(u64::MAX)] {
            assert!(annihilates(a) && identities(a));
        }
        assert_eq!(Tropical(3).add(&Tropical(5)), Tropical(3)); // min
        assert_eq!(Tropical(3).mul(&Tropical(5)), Tropical(8)); // +
    }

    #[test]
    fn ring_laws() {
        for a in [-5i64, 0, 7, i64::MAX, i64::MIN] {
            assert!(ring_law(a), "i64 ring law at {a}");
        }
        for a in [Gf2(false), Gf2(true)] {
            assert!(ring_law(a), "GF(2) ring law");
        }
        assert_eq!(10i64.sub(&3), 7);
        assert_eq!(Gf2(true).add(&Gf2(true)), Gf2(false)); // A xor A = empty
        assert_eq!(Gf2(true).add(&Gf2(false)), Gf2(true));
    }

    #[test]
    fn large_weight_is_mut_native() {
        // Poly (Clone, not Copy) — the case the value-only Copy design locked
        // out. In-place add extends and sums without a fresh allocation when
        // the right operand fits.
        let mut p = Poly(vec![1, 2, 3]);
        p.add_assign(&Poly(vec![10, 20]));
        assert_eq!(p, Poly(vec![11, 22, 3]));

        // semiring + ring laws hold for the large weight too
        let (a, b, c) = (Poly(vec![1, 1]), Poly(vec![2]), Poly(vec![3]));
        assert!(distributes(a.clone(), b.clone(), c.clone()));
        assert!(annihilates(a.clone()) && identities(a.clone()));
        assert!(ring_law(a));

        // * = convolution: (1 + x)(1 + x) = 1 + 2x + x^2
        assert_eq!(Poly(vec![1, 1]).mul(&Poly(vec![1, 1])), Poly(vec![1, 2, 1]));
    }

    #[test]
    fn value_form_is_defaulted() {
        // Every value op is the default over its _assign primitive.
        assert_eq!(2i64.add(&3).mul(&4), 20); // (2+3)*4
        assert!(true.mul(&false).add(&true));
    }

    #[test]
    fn weight_is_an_absorb_sink() {
        use crate::base::Absorb;
        // a weight folds items by ⊕; seed at zero() (= Default here)
        let mut acc = Tropical::default(); // = zero() = +inf
        for w in [Tropical(5), Tropical(2), Tropical(9)] {
            acc.absorb(w); // ⊕ = min
        }
        assert_eq!(acc, Tropical(2)); // min over the three
                                      // Poly as a sink: ⊕ = elementwise sum, in place
        let mut p = Poly::default(); // = zero() = empty
        for w in [Poly(vec![1, 2]), Poly(vec![10]), Poly(vec![0, 0, 3])] {
            p.absorb(w);
        }
        assert_eq!(p, Poly(vec![11, 2, 3]));
    }

    #[test]
    fn bool_is_the_recognizer_algebra() {
        assert!(true.add(&false));
        assert!(!true.mul(&false));
        assert!(true.add(&true));
    }
}
