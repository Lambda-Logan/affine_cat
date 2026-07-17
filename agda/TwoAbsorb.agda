{-# OPTIONS --safe #-}
-- Two-sorted absorption, mechanized — and the mechanization corrected
-- the shipped law set. The generated docs stated per-sort annihilation;
-- the proof demands it in BUBBLE form: at every hole, the reduce applied
-- to a bubble's reading at that sort equals the bubble's reading at the
-- node's sort. For same-sort bubbles this is ordinary annihilation; for
-- CROSS-SORT bubbles it additionally requires promotes to act as
-- sections on absorbed values (fvex (p12 x) ≡ x). Algebras that absorb
-- at one sort only (the resolver) satisfy the cross cases vacuously;
-- shared-error Result carriers satisfy them by Err-passthrough; lossy
-- promotes with double-crossing bubbles CANNOT — now a stated obligation.
--
--   T-X  agreeV/agreeR : the either-bubble driver, unwrapped at entry,
--        equals the plain mutual fold, given bubble-form annihilation.

module TwoAbsorb where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

data V : Set
data R : Set
data V where
  vlit : ℕ → V
  vex  : R → V
data R where
  rlit : ℕ → R
  rfil : R → V → R

record Alg2 (O1 O2 : Set) : Set where
  field
    fvlit : ℕ → O1
    fvex  : O2 → O1
    frlit : ℕ → O2
    frfil : O2 → O1 → O2
    ab1   : O1 → Bool
    ab2   : O2 → Bool
    p12   : O1 → O2
    p21   : O2 → O1

module Fold {O1 O2 : Set} (A : Alg2 O1 O2) where
  open Alg2 A

  foldV : V → O1
  foldR : R → O2
  foldV (vlit n)   = fvlit n
  foldV (vex r)    = fvex (foldR r)
  foldR (rlit n)   = frlit n
  foldR (rfil r v) = frfil (foldR r) (foldV v)

  data Brk : Set where
    b1 : O1 → Brk
    b2 : O2 → Brk

  pr1 : Brk → O1
  pr1 (b1 x) = x
  pr1 (b2 y) = p21 y

  pr2 : Brk → O2
  pr2 (b1 x) = p12 x
  pr2 (b2 y) = y

  data CF (X : Set) : Set where
    cont : X → CF X
    brk  : Brk → CF X

  chk1 : O1 → CF O1
  chk1 x with ab1 x
  ... | true  = brk (b1 x)
  ... | false = cont x

  chk2 : O2 → CF O2
  chk2 y with ab2 y
  ... | true  = brk (b2 y)
  ... | false = cont y

  tfV : V → CF O1
  tfR : R → CF O2
  tfV (vlit n) = chk1 (fvlit n)
  tfV (vex r) with tfR r
  ... | brk b  = brk b
  ... | cont y = chk1 (fvex y)
  tfR (rlit n) = chk2 (frlit n)
  tfR (rfil r v) with tfR r
  ... | brk b = brk b
  ... | cont y with tfV v
  ...   | brk b  = brk b
  ...   | cont x = chk2 (frfil y x)

  unV : CF O1 → O1
  unV (cont x) = x
  unV (brk b)  = pr1 b

  unR : CF O2 → O2
  unR (cont y) = y
  unR (brk b)  = pr2 b

  -- the law set the proof demands: annihilation in BUBBLE form
  record Laws : Set where
    field
      vexA  : ∀ b → fvex (pr2 b) ≡ pr1 b
      filAr : ∀ b x → frfil (pr2 b) x ≡ pr2 b
      filAv : ∀ y b → frfil y (pr1 b) ≡ pr2 b
    -- (each hypothesis is used only at bubbles the driver actually
    -- produced — i.e. absorbing ones; stating them unconditionally
    -- keeps the record small, and conditional versions restricted to
    -- absorbing bubbles prove the same theorem with more plumbing.)

  module Agree (L : Laws) where
    open Laws L

    chk1-cont : ∀ x {w} → chk1 x ≡ cont w → x ≡ w
    chk1-cont x eq with ab1 x
    chk1-cont x refl | false = refl

    chk1-brk : ∀ x {b} → chk1 x ≡ brk b → b ≡ b1 x
    chk1-brk x eq with ab1 x
    chk1-brk x refl | true = refl

    chk2-cont : ∀ y {w} → chk2 y ≡ cont w → y ≡ w
    chk2-cont y eq with ab2 y
    chk2-cont y refl | false = refl

    chk2-brk : ∀ y {b} → chk2 y ≡ brk b → b ≡ b2 y
    chk2-brk y eq with ab2 y
    chk2-brk y refl | true = refl

    -- the mutual invariant: cont carries the fold; a bubble READS as the
    -- fold at both sorts
    InvV : V → CF O1 → Set
    InvV t (cont x) = x ≡ foldV t
    InvV t (brk b)  = pr1 b ≡ foldV t

    InvR : R → CF O2 → Set
    InvR t (cont y) = y ≡ foldR t
    InvR t (brk b)  = pr2 b ≡ foldR t

    invV : ∀ t → InvV t (tfV t)
    invR : ∀ t → InvR t (tfR t)

    invV (vlit n) with chk1 (fvlit n) in eq
    ... | cont x = sym (chk1-cont (fvlit n) eq)
    ... | brk b rewrite chk1-brk (fvlit n) eq = refl
    invV (vex r) with tfR r in eqr
    ... | brk b =
          let ih : pr2 b ≡ foldR r
              ih = subst (InvR r) eqr (invR r)
          in trans (sym (vexA b)) (cong fvex ih)
    ... | cont y with chk1 (fvex y) in eqc
    ...   | cont x =
            let ih : y ≡ foldR r
                ih = subst (InvR r) eqr (invR r)
            in trans (sym (chk1-cont (fvex y) eqc)) (cong fvex ih)
    ...   | brk b rewrite chk1-brk (fvex y) eqc =
            let ih : y ≡ foldR r
                ih = subst (InvR r) eqr (invR r)
            in cong fvex ih

    invR (rlit n) with chk2 (frlit n) in eq
    ... | cont y = sym (chk2-cont (frlit n) eq)
    ... | brk b rewrite chk2-brk (frlit n) eq = refl
    invR (rfil r v) with tfR r in eqr
    ... | brk b =
          let ih : pr2 b ≡ foldR r
              ih = subst (InvR r) eqr (invR r)
          in trans (sym (filAr b (foldV v))) (cong (λ z → frfil z (foldV v)) ih)
    ... | cont y with tfV v in eqv
    ...   | brk b =
            let ihr : y ≡ foldR r
                ihr = subst (InvR r) eqr (invR r)
                ihv : pr1 b ≡ foldV v
                ihv = subst (InvV v) eqv (invV v)
            in trans (sym (filAv y b))
                     (trans (cong (frfil y) ihv) (cong (λ z → frfil z (foldV v)) ihr))
    ...   | cont x with chk2 (frfil y x) in eqc
    ...     | cont w =
              let ihr = subst (InvR r) eqr (invR r)
                  ihv = subst (InvV v) eqv (invV v)
              in trans (sym (chk2-cont (frfil y x) eqc))
                       (cong₂ frfil ihr ihv)
    ...     | brk b rewrite chk2-brk (frfil y x) eqc =
              let ihr = subst (InvR r) eqr (invR r)
                  ihv = subst (InvV v) eqv (invV v)
              in cong₂ frfil ihr ihv

    -- T-X: the public drivers agree with the plain fold
    agreeV : ∀ t → unV (tfV t) ≡ foldV t
    agreeV t with tfV t in eq
    ... | cont x = subst (InvV t) eq (invV t)
    ... | brk b  = subst (InvV t) eq (invV t)

    agreeR : ∀ t → unR (tfR t) ≡ foldR t
    agreeR t with tfR t in eq
    ... | cont y = subst (InvR t) eq (invR t)
    ... | brk b  = subst (InvR t) eq (invR t)
