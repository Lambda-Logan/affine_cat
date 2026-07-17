{-# OPTIONS --safe #-}
-- The COMPOSITION: scoped environments (AbsorbEnv) × cross-sort bubbles
-- (TwoAbsorb). Neither file covers `try_fold_in2`: AbsorbEnv's balance
-- is single-sort, TwoAbsorb's agreement is env-free. This file threads
-- both through one driver, faithful to the generated code:
--
--   * scoped holes bracket (enter = suc, restore on EVERY exit — the
--     restore-on-bubble is AbsorbEnv's guard theorem `brkAb`, taken as
--     licensed at each bracket, not re-proven);
--   * unscoped holes thread the env sequentially;
--   * reduces READ the env (depth-indexed algebras);
--   * bubbles cross sorts and exit through a promote.
--
-- Theorems:
--   B2X  balV/balR : the try-drivers are balanced — the returned env is
--        the entry env, on the continue path and the bubble path alike.
--   T2X  agreeV/agreeR : the drivers agree with the plain scoped mutual
--        fold, under bubble-form annihilation — which the composition
--        forces to be ENV-UNIFORM: a bubble transits scopes, so its
--        annihilation must hold at every depth on the way out. A reduce
--        whose absorption license held only in some scopes would break
--        agreement silently. (Err-passthrough is depth-blind: fine.)

module ScopedAbsorb where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

data V : Set
data R : Set
data V where
  vlit : ℕ → V
  vex  : R → V          -- scoped hole (Exists)
data R where
  rlit : ℕ → R
  rfil : R → V → R      -- unscoped R hole, then scoped V hole (Filter)

-- depth-reading two-sorted algebra with promotes
record Alg2E (O1 O2 : Set) : Set where
  field
    fvlit : ℕ → ℕ → O1
    fvex  : ℕ → O2 → O1
    frlit : ℕ → ℕ → O2
    frfil : ℕ → O2 → O1 → O2
    ab1   : O1 → Bool
    ab2   : O2 → Bool
    p12   : O1 → O2
    p21   : O2 → O1

-- `ew` is the env's `enter_with`: the frame for rfil's SCOPED V child
-- is computed from the preceding hole's folded value — `scope_prev`,
-- exactly as shipped (mutual.rs Filter). Plain `scope` is ew = const suc
-- (which vex below uses); the file covers both attributes.
module Fold {O1 O2 : Set} (A : Alg2E O1 O2) (ew : O2 → ℕ → ℕ) where
  open Alg2E A

  -- the plain scoped mutual fold (driver-owned, balanced motion)
  foldV : ℕ → V → O1
  foldR : ℕ → R → O2
  foldV d (vlit n)   = fvlit d n
  foldV d (vex r)    = fvex d (foldR (suc d) r)
  foldR d (rlit n)   = frlit d n
  foldR d (rfil r v) = frfil d (foldR d r) (foldV (ew (foldR d r) d) v)

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

  -- the composed try-drivers: env threaded, brackets restore on every
  -- exit (the guard), reduces read the env
  tfV : ℕ → V → CF O1 × ℕ
  tfR : ℕ → R → CF O2 × ℕ
  tfV d (vlit n) = chk1 (fvlit d n) , d
  tfV d (vex r) with tfR (suc d) r      -- ENTER; guard restores below
  ... | (brk b , _)  = brk b , d        -- restore on the BUBBLE path
  ... | (cont y , _) = chk1 (fvex d y) , d
  tfR d (rlit n) = chk2 (frlit d n) , d
  tfR d (rfil r v) with tfR d r         -- unscoped: thread
  ... | (brk b , d₁)  = brk b , d₁
  ... | (cont y , d₁) with tfV (ew y d₁) v  -- ENTER WITH the sibling fold
  ...   | (brk b , _)  = brk b , d₁         -- restore on bubble
  ...   | (cont x , _) = chk2 (frfil d₁ y x) , d₁

  unV : CF O1 → O1
  unV (cont x) = x
  unV (brk b)  = pr1 b

  unR : CF O2 → O2
  unR (cont y) = y
  unR (brk b)  = pr2 b

  ------------------------------------------------------------------
  -- B2X: balance of the composed drivers, bubble path included
  ------------------------------------------------------------------
  balV : ∀ d t → proj₂ (tfV d t) ≡ d
  balR : ∀ d t → proj₂ (tfR d t) ≡ d
  balV d (vlit n) = refl
  balV d (vex r) with tfR (suc d) r
  ... | (brk b , _)  = refl
  ... | (cont y , _) = refl
  balR d (rlit n) = refl
  balR d (rfil r v) with tfR d r in eqr
  ... | (brk b , d₁)  = trans (sym (cong proj₂ eqr)) (balR d r)
  ... | (cont y , d₁) with tfV (ew y d₁) v
  ...   | (brk b , _)  = trans (sym (cong proj₂ eqr)) (balR d r)
  ...   | (cont x , _) = trans (sym (cong proj₂ eqr)) (balR d r)

  ------------------------------------------------------------------
  -- the law set: bubble-form annihilation, ENV-UNIFORM
  ------------------------------------------------------------------
  record Laws : Set where
    field
      vexA  : ∀ d b → fvex d (pr2 b) ≡ pr1 b
      filAr : ∀ d b x → frfil d (pr2 b) x ≡ pr2 b
      filAv : ∀ d y b → frfil d y (pr1 b) ≡ pr2 b

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

    InvV : ℕ → V → CF O1 → Set
    InvV d t (cont x) = x ≡ foldV d t
    InvV d t (brk b)  = pr1 b ≡ foldV d t

    InvR : ℕ → R → CF O2 → Set
    InvR d t (cont y) = y ≡ foldR d t
    InvR d t (brk b)  = pr2 b ≡ foldR d t

    -- checking a correct value preserves the invariant, cont or brk
    chk1-inv : ∀ dd tt z → z ≡ foldV dd tt → InvV dd tt (chk1 z)
    chk2-inv : ∀ dd tt z → z ≡ foldR dd tt → InvR dd tt (chk2 z)

    chk1-inv dd tt z zeq with chk1 z in eq
    ... | cont w = trans (sym (chk1-cont z eq)) zeq
    ... | brk b rewrite chk1-brk z eq = zeq

    chk2-inv dd tt z zeq with chk2 z in eq
    ... | cont w = trans (sym (chk2-cont z eq)) zeq
    ... | brk b rewrite chk2-brk z eq = zeq

    invV : ∀ d t → InvV d t (proj₁ (tfV d t))
    invR : ∀ d t → InvR d t (proj₁ (tfR d t))

    invV d (vlit n) = chk1-inv d (vlit n) (fvlit d n) refl
    invV d (vex r) with tfR (suc d) r in eqr
    ... | (brk b , _) =
          let ih : pr2 b ≡ foldR (suc d) r
              ih = subst (InvR (suc d) r) (cong proj₁ eqr) (invR (suc d) r)
          in trans (sym (vexA d b)) (cong (fvex d) ih)
    ... | (cont y , _) =
          let ih : y ≡ foldR (suc d) r
              ih = subst (InvR (suc d) r) (cong proj₁ eqr) (invR (suc d) r)
          in chk1-inv d (vex r) (fvex d y) (cong (fvex d) ih)

    invR d (rlit n) = chk2-inv d (rlit n) (frlit d n) refl
    invR d (rfil r v) with tfR d r in eqr
    ... | (brk b , d₁) =
          let ih : pr2 b ≡ foldR d r
              ih = subst (InvR d r) (cong proj₁ eqr) (invR d r)
          in trans (sym (filAr d b (foldV (ew (foldR d r) d) v)))
                   (cong (λ z → frfil d z (foldV (ew (foldR d r) d) v)) ih)
    ... | (cont y , d₁) with tfV (ew y d₁) v in eqv
    ...   | (brk b , _) =
            let deq : d₁ ≡ d
                deq = trans (sym (cong proj₂ eqr)) (balR d r)
                ihr : y ≡ foldR d r
                ihr = subst (InvR d r) (cong proj₁ eqr) (invR d r)
                eweq : ew y d₁ ≡ ew (foldR d r) d
                eweq = cong₂ ew ihr deq
                ihv : pr1 b ≡ foldV (ew y d₁) v
                ihv = subst (InvV (ew y d₁) v) (cong proj₁ eqv) (invV (ew y d₁) v)
                ihv' : pr1 b ≡ foldV (ew (foldR d r) d) v
                ihv' = trans ihv (cong (λ k → foldV k v) eweq)
            in trans (sym (filAv d (foldR d r) b))
                     (cong (frfil d (foldR d r)) ihv')
    ...   | (cont x , _) =
            let deq : d₁ ≡ d
                deq = trans (sym (cong proj₂ eqr)) (balR d r)
                ihr : y ≡ foldR d r
                ihr = subst (InvR d r) (cong proj₁ eqr) (invR d r)
                eweq : ew y d₁ ≡ ew (foldR d r) d
                eweq = cong₂ ew ihr deq
                ihv : x ≡ foldV (ew y d₁) v
                ihv = subst (InvV (ew y d₁) v) (cong proj₁ eqv) (invV (ew y d₁) v)
                ihv' : x ≡ foldV (ew (foldR d r) d) v
                ihv' = trans ihv (cong (λ k → foldV k v) eweq)
                red : frfil d₁ y x ≡ frfil d (foldR d r) (foldV (ew (foldR d r) d) v)
                red = trans (cong (λ k → frfil k y x) deq)
                            (cong₂ (frfil d) ihr ihv')
            in chk2-inv d (rfil r v) (frfil d₁ y x) red

    -- T2X: the public drivers agree with the plain scoped fold
    agreeV : ∀ d t → unV (proj₁ (tfV d t)) ≡ foldV d t
    agreeV d t with proj₁ (tfV d t) in eq
    ... | cont x = subst (InvV d t) eq (invV d t)
    ... | brk b  = subst (InvV d t) eq (invV d t)

    agreeR : ∀ d t → unR (proj₁ (tfR d t)) ≡ foldR d t
    agreeR d t with proj₁ (tfR d t) in eq
    ... | cont y = subst (InvR d t) eq (invR d t)
    ... | brk b  = subst (InvR d t) eq (invR d t)
