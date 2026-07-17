{-# OPTIONS --safe #-}
-- The order-permutation theorem (A1's residue): traversal order is
-- contract because it is OBSERVABLE — through absorption priority, env
-- motion, and codata forcing. This file proves the complement: for
-- env-INSENSITIVE algebras on the plain fold, order cannot be observed —
-- the swapped-children driver computes the same values.
module Order where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import AbsorbEnv using (E; lit; add; scope; EF; litL; addL; scopeL; Alg; foldE; balE)

-- the swapped driver: y before x at add (env threaded in that order)
foldE' : ∀ {B} → Alg B → ℕ → E → B × ℕ
foldE' a d (lit n) = a d (litL n) , d
foldE' a d (add x y) =
  let py = foldE' a d y
      px = foldE' a (proj₂ py) x
  in a (proj₂ px) (addL (proj₁ px) (proj₁ py)) , proj₂ px
foldE' a d (scope e) =
  let pe = foldE' a (suc d) e
  in a d (scopeL (proj₁ pe)) , d

balE' : ∀ {B} (a : Alg B) d e → proj₂ (foldE' a d e) ≡ d
balE' a d (lit n) = refl
balE' a d (add x y) rewrite balE' a d y | balE' a d x = refl
balE' a d (scope e) = refl

-- UNCONDITIONAL: bracketed driver-owned motion means every reduce sees
-- its node's entry depth regardless of sibling order — no insensitivity
-- hypothesis needed. This is the discipline's payoff as a theorem: the
-- balanced driver makes plain-fold order unobservable for ALL algebras.
-- (Absorption priority and codata forcing remain order-observable; the
-- contract stands for those.)
order-perm : ∀ {B} (a : Alg B) →
             ∀ d e → proj₁ (foldE' a d e) ≡ proj₁ (foldE a d e)
order-perm a d (lit n) = refl
order-perm a d (add x y)
  rewrite balE' a d y | balE' a d x | balE a d x | balE a d y
        | order-perm a d x | order-perm a d y
  = refl
order-perm a d (scope e)
  rewrite order-perm a (suc d) e = refl

------------------------------------------------------------------------
-- The contract's other tail, exhibited: absorption order IS observable.
-- Two absorbing children; the left-first and right-first try-drivers
-- return DIFFERENT values on the same tree and algebra. This is why
-- "order is contract" survives order-perm above: the unconditional
-- theorem covers the plain fold only; absorption reintroduces order.
module AbsorbOrderObservable where
  open import Data.Bool using (Bool; true; false)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Nullary using (¬_)
  open import Data.Empty using (⊥)

  data T : Set where
    two : ℕ → ℕ → T

  data CF : Set where
    cont : ℕ → CF
    brk  : ℕ → CF

  -- the try-driver shape: check each child, first absorber wins;
  -- the algebra: everything absorbs (ab ≡ true), reduce = sum
  chk : ℕ → CF
  chk n = brk n -- ab n ≡ true for all n

  tfL : T → CF -- left first
  tfL (two x y) with chk x
  ... | brk b  = brk b
  ... | cont _ = chk y

  tfR : T → CF -- right first
  tfR (two x y) with chk y
  ... | brk b  = brk b
  ... | cont _ = chk x

  witness-L : tfL (two 1 2) ≡ brk 1
  witness-L = refl

  witness-R : tfR (two 1 2) ≡ brk 2
  witness-R = refl

  order-observable : ¬ (tfL (two 1 2) ≡ tfR (two 1 2))
  order-observable ()
