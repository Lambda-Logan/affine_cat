{-# OPTIONS --safe --without-K #-}
-- The comonoid layer of the frame, made precise in (Set, ×, ⊤).
--
-- The crate organizes "which objects may be copied" through `Unaliased`.
-- The frame's claim is that this is the *comonoid* structure of a
-- semicartesian (= affine) monoidal category, and that the copy map is
-- not a design choice but is FORCED. This module mechanizes exactly that
-- forcing, in the concrete model where objects are Sets:
--
--   T-DEL   del-unique   : the counit A → ⊤ is unique (⊤ terminal) — the
--           "everything drops" half of affine, with no freedom.
--   T-DUP   dup-unique   : ANY comultiplication satisfying the two counit
--           laws EQUALS the diagonal `λ x → (x , x)`. Copyability is a
--           property, not extra data: if a lawful copy exists it is the
--           diagonal, uniquely.
--   T-LAW   diagonal is a comonoid: the diagonal satisfies both counit
--           laws and coassociativity (all refl — the laws hold on the
--           nose for the forced map).
--
-- What is DELIBERATELY NOT here (named, not hidden — these are seams
-- where Agda is the wrong term-former):
--  * That `&Cell<T>` is `Copy` yet fails this — that is a statement about
--    Rust's *operational* semantics (mutate through one alias, observe
--    through another), a Rust-witness obligation, not an Agda one. The
--    frame's payoff — `Unaliased` ≠ `Copy` — lives at that seam.
--  * The universal property "free semicartesian SMC on Rust's types"
--    needs an abstract-category setting this concrete `Set` model does
--    not provide. Mechanized here: the equational/uniqueness content.

module Comonoid where

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

private variable A X : Set

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

cong : {A B : Set}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set}(f : A → B → C){x y : A}{u v : B}
      → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

-- η for pairs is definitional in Agda: p ≡ (fst p , snd p) is refl. So a
-- pair is equal to the pair of its verified components.
pair-≡ : {a : A}{b : X}(p : A × X) → fst p ≡ a → snd p ≡ b → p ≡ (a , b)
pair-≡ p fp sp = cong₂ _,_ fp sp

------------------------------------------------------------------------
-- T-DEL : the counit is unique because ⊤ is terminal.
------------------------------------------------------------------------
del-unique : (del : X → ⊤) → ∀ x → del x ≡ tt
del-unique del x with del x
... | tt = refl

------------------------------------------------------------------------
-- T-DUP : the two counit laws force the diagonal.
--
-- counit-l / counit-r are the comonoid counit laws AFTER the left/right
-- unitors ⊤ × X ≅ X ≅ X × ⊤ are applied, which in Set are just the
-- projections. So the laws read: the first (resp. second) projection of
-- `dup x` is `x`. Together they pin `dup` to the diagonal.
------------------------------------------------------------------------
dup-unique : (dup : X → X × X)
           → (∀ x → fst (dup x) ≡ x)   -- counit-l
           → (∀ x → snd (dup x) ≡ x)   -- counit-r
           → ∀ x → dup x ≡ (x , x)
dup-unique dup cl cr x = pair-≡ (dup x) (cl x) (cr x)

------------------------------------------------------------------------
-- T-LAW : the forced map IS a lawful comonoid.
------------------------------------------------------------------------
diagonal : X → X × X
diagonal x = (x , x)

del : X → ⊤
del _ = tt

-- counit laws hold on the nose
counit-l : (x : X) → fst (diagonal x) ≡ x
counit-l x = refl

counit-r : (x : X) → snd (diagonal x) ≡ x
counit-r x = refl

-- coassociativity: (Δ × id) ∘ Δ  ≡  assoc ∘ (id × Δ) ∘ Δ.
-- LHS x = ((x , x) , x) ; (id × Δ) ∘ Δ gives (x , (x , x)); the
-- associator ⟨⟨a,b⟩,c⟩ ↦ ⟨a,⟨b,c⟩⟩ closes the triangle — all refl.
assoc× : {A B C : Set} → (A × B) × C → A × (B × C)
assoc× ((a , b) , c) = (a , (b , c))

-- (Δ ⊗ id) ∘ Δ  : X → (X × X) × X
dupL : X → (X × X) × X
dupL x = (diagonal (fst (diagonal x)) , snd (diagonal x))

-- (id ⊗ Δ) ∘ Δ  : X → X × (X × X)
dupR : X → X × (X × X)
dupR x = (fst (diagonal x) , diagonal (snd (diagonal x)))

-- coassociativity: the two rebracketings agree through the associator.
coassoc : (x : X) → assoc× (dupL x) ≡ dupR x
coassoc x = refl

-- cocommutativity (the diagonal is symmetric): swap ∘ Δ ≡ Δ. This is why
-- the copy is a *cocommutative* comonoid — the datum a cartesian object
-- carries. (Not needed for uniqueness; recorded because the frame calls
-- the objects cocommutative comonoids specifically.)
swap : {A B : Set} → A × B → B × A
swap (a , b) = (b , a)

cocomm : (x : X) → swap (diagonal x) ≡ diagonal x
cocomm x = refl
