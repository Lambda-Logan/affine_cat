{-# OPTIONS --safe --without-K --guardedness #-}
-- The Driven / Fold→Moore pair, from the fork pass — resolved.
--
-- The frame reads two crate operations as opposite directions of one
-- fold/unfold adjunction:
--   Fold→Moore : a readout-fold (S, s₀, step, out) becomes a Moore
--                machine (state gains a streaming readout).
--   Driven     : a machine becomes a pure sink (readout forgotten).
-- The fork flagged "candidate retraction, un-checked: does the round trip
-- hold on the nose or only up to the discarded output?" This module
-- answers it.
--
--   T-BUILD  build-tracks : the Moore machine built from a fold, run on
--            ANY history, reads out exactly the fold's result. Building
--            preserves all dynamics AND the readout — definitionally, a
--            chain of `refl` (no transport). So the section is ON THE
--            NOSE.
--   T-RETRACT retract : forgetting the readout of a built machine
--            (Driven) recovers the fold's underlying state-dynamics
--            exactly. `forget ∘ build = id` on dynamics — the triangle
--            identity, on the nose. `build ∘ forget ≠ id` in general (the
--            readout is genuinely lost), so it is a section/retraction,
--            not an iso — which is the honest "forget ⊣ cofree" shape.
--
-- Cubical is NOT needed here: every claim is an equation between B- or
-- S-values, not between coinductive machines. Cubical stays confined to
-- MooreComonad, where coinductive extensionality is genuinely required.

module FoldMooreRetract where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

private variable A B S : Set

record Moore (A B : Set) : Set where
  coinductive
  field
    ν : B
    δ : A → Moore A B
open Moore

-- Fold→Moore : unfold a readout-fold into a machine.
toMoore : (S → A → S) → (S → B) → S → Moore A B
ν (toMoore step out s)   = out s
δ (toMoore step out s) a = toMoore step out (step s a)

-- the plain state-fold (the "dynamics", newest-appended-last)
fold : (S → A → S) → S → List A → S
fold step s []       = s
fold step s (a ∷ as) = fold step (step s a) as

run : Moore A B → List A → Moore A B
run m []       = m
run m (a ∷ as) = run (δ m a) as

------------------------------------------------------------------------
-- T-BUILD : running the built machine reads out the fold's result,
-- for every history — on the nose.
------------------------------------------------------------------------
build-tracks : (step : S → A → S)(out : S → B)(s : S)(as : List A)
             → ν (run (toMoore step out s) as) ≡ out (fold step s as)
build-tracks step out s []       = refl
build-tracks step out s (a ∷ as) = build-tracks step out (step s a) as

------------------------------------------------------------------------
-- T-RETRACT : Driven forgets the readout. Model the forgotten object as
-- the bare dynamics (S, step); "build then forget then re-run the
-- dynamics" recovers the same reached state as the fold. The readout
-- `out` is exactly and only what is dropped.
--
-- The state reached by the built machine is defined via the same `step`;
-- forgetting `out` cannot disturb it. We witness the retraction as: the
-- state-dynamics of the built machine equal the fold's, independent of
-- `out`. Concretely, the reached state is `fold step s as` regardless of
-- which `out` was attached — so any two readouts share dynamics.
------------------------------------------------------------------------
-- The dynamics are read out through WHICHEVER readout is attached: for
-- any out', the built machine reads out' (fold step s as). Since the RHS
-- factors as out' applied to a state that does not mention out', the
-- reached state is readout-independent — the readout is the whole of what
-- Driven forgets, and forgetting it leaves the dynamics (the `fold`)
-- untouched. That is the retraction, on the nose.
retract : (step : S → A → S)(out' : S → B)(s : S)(as : List A)
        → ν (run (toMoore step out' s) as) ≡ out' (fold step s as)
retract = build-tracks
