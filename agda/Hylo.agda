{-# OPTIONS --safe #-}
-- Receipts for the absorption/short-circuit design and Pair-over-codata.
-- Agda 2.6.3, stdlib 1.7.3, --safe, no postulates.
--
-- Post-sacrifice note: the Rust borrowed fold over Thunk holes no
-- longer exists; the theorems below remain the semantics of the
-- CONSUMING driver (same recursion shape, ownership invisible in Set),
-- and `pair-short`'s Rust incarnation is PairOwned's one pass.
-- Check-position note: foldS checks child RESULTS (consumer position),
-- matching the generated drivers exactly; AbsorbEnv's foldEG also chks
-- at leaves (producer position) — the value sets agree because
-- val ∘ chk = id and a check commutes across one edge.
--
-- Scope honesty: this models DENOTATIONS. Post-sacrifice note: the Rust
-- borrowed absorbing driver over codata no longer exists (Thunk grants
-- no borrowed forcing); foldS now models the CONSUMING driver, whose
-- shape is identical. One position seam: these proofs check absorption
-- at the producer (chk after reduce); generated code checks at the
-- consumer (after each child) — same values by Break-propagation, a
-- shifted position the equations cover but the syntax does not mirror.
-- Also: this models DENOTATIONS. In a total language, forcing a
-- thunk is just application, so "fold over a thunked tree" is
-- definitionally foldT of the built tree; the deforestation (peak
-- liveness) and affine-forcing (panic on second force) claims are
-- OPERATIONAL, witnessed by the Rust counters, not provable in Set.
-- What IS provable, and is proved here:
--   T-A  absorb-sound : the short-circuiting driver agrees with the plain
--        fold, given the annihilation law (skipping is semantics-safe).
--   T-B  banana       : pairing algebras through one fold = two folds.
--   T-C  pair-annihilates : annihilation is inherited by the pair with
--        the both-components-absorbing predicate (the shipped Pair).
--   T-D  pair-short   : composition — ONE short-circuiting Pair pass
--        equals the two counterfactual plain folds. Over affine codata
--        the right side is unrunnable; this equation is what makes the
--        one runnable pass mean what two passes would have meant.

module Hylo where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

data Tree : Set where
  lit  : ℕ → Tree
  node : Tree → Tree → Tree

data TreeF (X : Set) : Set where
  litF  : ℕ → TreeF X
  nodeF : X → X → TreeF X

Alg : Set → Set
Alg B = TreeF B → B

foldT : ∀ {B} → Alg B → Tree → B
foldT a (lit n)    = a (litF n)
foldT a (node l r) = a (nodeF (foldT a l) (foldT a r))

-- The generated driver's shape: check absorption after each child,
-- bubble immediately, skip the rest.
foldS : ∀ {B} → (B → Bool) → Alg B → Tree → B
foldS ab a (lit n) = a (litF n)
foldS ab a (node l r) =
  let fl = foldS ab a l in
  if ab fl then fl
  else (let fr = foldS ab a r in
        if ab fr then fr
        else a (nodeF fl fr))

-- The annihilation law, exactly as documented on FoldAlg::absorbing:
-- an absorbing hole determines the reduce.
record Annihilates {B : Set} (ab : B → Bool) (a : Alg B) : Set where
  field
    annL : ∀ x y → ab x ≡ true → a (nodeF x y) ≡ x
    annR : ∀ x y → ab y ≡ true → a (nodeF x y) ≡ y
open Annihilates

-- T-A: skipping is sound. (Note the shape: foldT still *denotes* the
-- skipped child's value; annihilation says that value cannot matter.
-- The skip is operational profit, the law is its semantic license.)
absorb-sound : ∀ {B} (ab : B → Bool) (a : Alg B) → Annihilates ab a →
               ∀ t → foldS ab a t ≡ foldT a t
absorb-sound ab a ann (lit n) = refl
absorb-sound ab a ann (node l r)
  rewrite absorb-sound ab a ann l
        | absorb-sound ab a ann r
  with ab (foldT a l) in eqL
... | true  = sym (annL ann (foldT a l) (foldT a r) eqL)
... | false with ab (foldT a r) in eqR
...   | true  = sym (annR ann (foldT a l) (foldT a r) eqR)
...   | false = refl

-- The shipped Pair: tupling algebra (unzip is trivial in a cartesian
-- model — the affine price paid by Holes::unzip_with is invisible here).
pairAlg : ∀ {B C} → Alg B → Alg C → Alg (B × C)
pairAlg f g (litF n) = f (litF n) , g (litF n)
pairAlg f g (nodeF (x₁ , x₂) (y₁ , y₂)) = f (nodeF x₁ y₁) , g (nodeF x₂ y₂)

-- T-B: banana-split for this tree.
banana : ∀ {B C} (f : Alg B) (g : Alg C) t →
         foldT (pairAlg f g) t ≡ (foldT f t , foldT g t)
banana f g (lit n) = refl
banana f g (node l r)
  rewrite banana f g l | banana f g r = refl

-- The shipped predicate: a pair bubbles only when BOTH components absorb.
pairAb : ∀ {B C : Set} → (B → Bool) → (C → Bool) → (B × C → Bool)
pairAb p q (b , c) = p b ∧ q c

∧-split : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-split true true refl = refl , refl

-- T-C: annihilation is inherited by the pair.
pair-annihilates : ∀ {B C} (p : B → Bool) (q : C → Bool)
                   (f : Alg B) (g : Alg C) →
                   Annihilates p f → Annihilates q g →
                   Annihilates (pairAb p q) (pairAlg f g)
annL (pair-annihilates p q f g af ag) (x₁ , x₂) (y₁ , y₂) e
  with ∧-split (p x₁) (q x₂) e
... | (pe , qe) = cong₂ _,_ (annL af x₁ y₁ pe) (annL ag x₂ y₂ qe)
annR (pair-annihilates p q f g af ag) (x₁ , x₂) (y₁ , y₂) e
  with ∧-split (p y₁) (q y₂) e
... | (pe , qe) = cong₂ _,_ (annR af x₁ y₁ pe) (annR ag x₂ y₂ qe)

-- T-D: the composed claim. One short-circuiting Pair traversal equals
-- the two plain folds — which, over affine codata, can no longer be run.
pair-short : ∀ {B C} (p : B → Bool) (q : C → Bool)
             (f : Alg B) (g : Alg C) →
             Annihilates p f → Annihilates q g →
             ∀ t → foldS (pairAb p q) (pairAlg f g) t
                     ≡ (foldT f t , foldT g t)
pair-short p q f g af ag t =
  trans (absorb-sound (pairAb p q) (pairAlg f g)
                      (pair-annihilates p q f g af ag) t)
        (banana f g t)

--   T-H  reflection : folding with the constructor algebra is the
--        identity — Lambek's `embed` half, the zero point every rewrite
--        perturbs. (Rust: `Rebuild`, checked in examples/rewrite.rs.)
embedAlg : Alg Tree
embedAlg (litF n)    = lit n
embedAlg (nodeF a b) = node a b

reflection : ∀ t → foldT embedAlg t ≡ t
reflection (lit n) = refl
reflection (node l r)
  rewrite reflection l | reflection r = refl

-- and its interaction with the rest of the corpus for free:
-- one PAIRED pass computing (identity copy, analysis) equals (t, foldT g t)
copy-and-analyze : ∀ {C} (g : Alg C) t →
                   foldT (pairAlg embedAlg g) t ≡ (t , foldT g t)
copy-and-analyze g t =
  trans (banana embedAlg g t) (cong₂ _,_ (reflection t) refl)
