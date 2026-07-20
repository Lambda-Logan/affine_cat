//! Weighted automata as readouts over the Moore product.
//!
//! A weighted automaton is a [`Machine`] whose output is a
//! [`crate::ringy::Semiring`] weight; a Boolean recognizer (`Out = bool`) is
//! its [`bool`] instance. This module provides the two product combinators:
//! [`Sum`] combines the two component readouts with `⊕` (union at `bool`),
//! [`Prod`] with `⊗` (intersection at `bool`).
//!
//! Both are [`crate::machines::DuplicateToMachine`] — the shared-input Moore
//! product — composed with a semiring operation on the readout pair. The
//! product structure (duplicate the input, advance both, pay the
//! [`crate::base::Unaliased`] bound) lives once in `DuplicateToMachine`; `Sum` and
//! `Prod` add only the `⊕`/`⊗` gate. At `S = bool` they *are* Boolean
//! recognizer union and intersection.
//!
//! Only the two operations that generalize live here. Complement (`Not`) and
//! difference stay bool-specific: complement needs Boolean-algebra structure
//! a general semiring lacks, and symmetric difference needs a ring (see
//! [`crate::ringy::Gf2`]).
//!
//! # Meaning by semiring
//! * `bool` `(∨, ∧)`: `Sum` = union of languages, `Prod` = intersection.
//! * `Tropical` `(min, +)`: `Sum` = min of two path costs, `Prod` = their sum.
//! * `u64` `(+, ×)`: `Sum` = total accepting-path count, `Prod` = product.
//! * `Viterbi` `(max, ×)`: `Sum` = better of two likelihoods.

use crate::base::Unaliased;
use crate::machines::{DuplicateToMachine, Machine};
use crate::ringy::Semiring;

/// The weighted **`⊕`-product**: run both machines over the shared input and
/// read out `a.out() ⊕ b.out()`. Generalizes Boolean union (which is
/// the `⊕`-product at `S = bool`, where `⊕ = ∨` gives language union).
#[derive(Debug, Clone, Copy, Default)]
pub struct Sum<A, B>(DuplicateToMachine<A, B>);

impl<A, B> Sum<A, B> {
    /// Build from the two component weighted machines.
    pub fn new(a: A, b: B) -> Self {
        Sum(DuplicateToMachine::new(a, b))
    }
}

impl<I, S, A, B> Machine for Sum<A, B>
where
    I: Unaliased,
    S: Semiring,
    A: Machine<In = I, Out = S>,
    B: Machine<In = I, Out = S>,
{
    type In = I;
    type Out = S;
    fn out(&self) -> S {
        let (a, b) = self.0.out();
        a.add(&b)
    }
    fn update(&mut self, i: I) {
        self.0.update(i);
    }
}

/// The weighted **`⊗`-product**: run both machines over the shared input and
/// read out `a.out() ⊗ b.out()`. Generalizes Boolean intersection (which is
/// the `⊗`-product at `S = bool`, where `⊗ = ∧` gives intersection).
#[derive(Debug, Clone, Copy, Default)]
pub struct Prod<A, B>(DuplicateToMachine<A, B>);

impl<A, B> Prod<A, B> {
    /// Build from the two component weighted machines.
    pub fn new(a: A, b: B) -> Self {
        Prod(DuplicateToMachine::new(a, b))
    }
}

impl<I, S, A, B> Machine for Prod<A, B>
where
    I: Unaliased,
    S: Semiring,
    A: Machine<In = I, Out = S>,
    B: Machine<In = I, Out = S>,
{
    type In = I;
    type Out = S;
    fn out(&self) -> S {
        let (a, b) = self.0.out();
        a.mul(&b)
    }
    fn update(&mut self, i: I) {
        self.0.update(i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machines::run_history;
    use crate::ringy::Tropical;

    // A weighted machine: accumulates a per-symbol cost via the semiring.
    #[derive(Clone, Copy)]
    struct Cost {
        target: char,
        step: Tropical,
        acc: Tropical,
    }
    impl Machine for Cost {
        type In = char;
        type Out = Tropical;
        fn out(&self) -> Tropical {
            self.acc
        }
        fn update(&mut self, c: char) {
            if c == self.target {
                self.acc.mul_assign(&self.step); // ⊗ = + in tropical
            }
        }
    }
    fn cost(target: char, per: u64) -> Cost {
        Cost {
            target,
            step: Tropical(per),
            acc: Tropical::one(),
        }
    }

    // A bool recognizer, to witness Sum/Prod = union/intersection at bool.
    #[derive(Clone, Copy)]
    struct Has(char, bool);
    impl Machine for Has {
        type In = char;
        type Out = bool;
        fn out(&self) -> bool {
            self.1
        }
        fn update(&mut self, c: char) {
            if c == self.0 {
                self.1 = true;
            }
        }
    }

    #[test]
    fn tropical_sum_is_min_cost_prod_is_total() {
        // Sum = min(costA, costB); Prod = costA + costB (tropical ⊗).
        for s in ["", "a", "b", "aab", "abb"] {
            let ca = {
                let mut m = cost('a', 1);
                run_history(&mut m, s.chars())
            };
            let cb = {
                let mut m = cost('b', 3);
                run_history(&mut m, s.chars())
            };
            let mut sum = Sum::new(cost('a', 1), cost('b', 3));
            assert_eq!(run_history(&mut sum, s.chars()), ca.add(&cb), "Sum {s:?}");
            let mut prod = Prod::new(cost('a', 1), cost('b', 3));
            assert_eq!(run_history(&mut prod, s.chars()), ca.mul(&cb), "Prod {s:?}");
        }
    }

    #[test]
    fn bool_instance_is_union_and_intersection() {
        // Sum at bool = union, Prod at bool = intersection.
        for s in ["", "a", "b", "ab"] {
            let mut sum = Sum::new(Has('a', false), Has('b', false));
            assert_eq!(
                run_history(&mut sum, s.chars()),
                s.contains('a') || s.contains('b')
            );
            let mut prod = Prod::new(Has('a', false), Has('b', false));
            assert_eq!(
                run_history(&mut prod, s.chars()),
                s.contains('a') && s.contains('b')
            );
        }
    }
}
