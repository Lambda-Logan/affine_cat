{-# OPTIONS --safe #-}
-- Gap-grams are a SHIFT, not a zip — the clock theorem behind the
-- Tee-note correction in lib.rs. Model: Moore machines stepping once
-- per token, so "one shared clock" is enforced BY THE TYPE of `step`.
-- A (k+1)-register delay line, paired with the identity register by the
-- Moore product, reads out (x_t , x_{t-k}) after one forward pass over
-- one input history. No suspended second producer appears anywhere in
-- the construction — so gap-shaped pairing over machines needs a delay
-- register and the product, not Tee. What Tee remains for, and what
-- this model excludes by construction, is two legs consuming at
-- DIFFERENT rates: `step : A -> St -> St` cannot decline a token.
-- (The Maybe in the readout is the warm-up story: histories shorter
-- than the gap read `nothing`, where creature_feature 0.1.7 panics at
-- gap_gram.rs:35 on the same inputs.)
--
--   T-D  delay-reads-back : register i of the delay line holds the
--        input i steps back, for every history and every register.
--   T-G  gap-pair : the product's readout after history h is
--        (at h 0 , at h k) — the gap pair, off one clock.

module GapClock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; inject₁; toℕ; fromℕ)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

module _ {A : Set} where

  -- newest-first history; `at h i` is the token i steps back
  at : List A → ℕ → Maybe A
  at []      _       = nothing
  at (x ∷ _) zero    = just x
  at (_ ∷ h) (suc n) = at h n

  -- the delay line: suc k Maybe-registers as a function-state Moore
  -- machine (register 0 newest). `Delay::by(k)` reads register k.
  D : ℕ → Set
  D k = Fin (suc k) → Maybe A

  d₀ : ∀ {k} → D k
  d₀ _ = nothing

  stepD : ∀ {k} → A → D k → D k
  stepD x r Fin.zero    = just x
  stepD x r (Fin.suc i) = r (inject₁ i)

  runD : ∀ {k} → List A → D k
  runD []      = d₀
  runD (x ∷ h) = stepD x (runD h)

  -- T-D: every register reads the history at its own depth
  delay-reads-back : ∀ {k} h (i : Fin (suc k)) → runD h i ≡ at h (toℕ i)
  delay-reads-back []      Fin.zero    = refl
  delay-reads-back []      (Fin.suc i) = refl
  delay-reads-back (x ∷ h) Fin.zero    = refl
  delay-reads-back (x ∷ h) (Fin.suc i) =
    trans (delay-reads-back h (inject₁ i)) (cong (at h) (toℕ-inject₁ i))

  -- the identity register (the "now" leg)
  I : Set
  I = Maybe A

  stepI : A → I → I
  stepI x _ = just x

  runI : List A → I
  runI []      = nothing
  runI (x ∷ h) = stepI x (runI h)

  now-reads-now : ∀ h → runI h ≡ at h 0
  now-reads-now []      = refl
  now-reads-now (x ∷ h) = refl

  -- the Moore product: BOTH components step on EVERY token — the one
  -- shared clock, visible as the type of stepP
  P : ℕ → Set
  P k = I × D k

  stepP : ∀ {k} → A → P k → P k
  stepP x (i , d) = stepI x i , stepD x d

  runP : ∀ {k} → List A → P k
  runP []      = nothing , d₀
  runP (x ∷ h) = stepP x (runP h)

  -- the product runs componentwise
  par : ∀ {k} (h : List A) → runP {k} h ≡ (runI h , runD h)
  par []      = refl
  par (x ∷ h) = cong (stepP x) (par h)

  -- T-G: one pass over one history yields the gap pair (x_t , x_{t-k})
  gap-pair : ∀ {k} (h : List A) →
      (proj₁ (runP {k} h) , proj₂ (runP {k} h) (fromℕ k)) ≡ (at h 0 , at h k)
  gap-pair {k} h = cong₂ _,_
    (trans (cong proj₁ (par h)) (now-reads-now h))
    (trans (cong (λ p → proj₂ p (fromℕ k)) (par h))
           (trans (delay-reads-back h (fromℕ k)) (cong (at h) (toℕ-fromℕ k))))
