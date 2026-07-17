{-# OPTIONS --safe #-}
-- Absorption meets scope motion. Model: single-sorted tree with a binder
-- node (`scope`), env = de Bruijn depth, driver owns motion (suc on
-- descent, restore-saved on return). This matches the shipped surface:
-- the derive is single-sorted; the two-sorted case is flagged in the
-- Rust docs as undesigned (a Break value has no sort-crossing type).
--
--   T-E  naive-leaks   : the naive short-circuit driver (Break skips the
--        restore) corrupts the environment — concrete counterexample.
--   T-F  balG          : the GUARDED driver (restore on the bubble path)
--        keeps context evolution a function of entry state, every path.
--   T-G  agree         : guarded short-circuiting fold ≡ strict fold
--        (value component), given per-context annihilation.
-- Together: the #[scope] codegen constraint — frame restoration belongs
-- on the unwind path — is now a theorem pair, not a doc warning.

-- Position note: foldEG chks leaf outputs (producer position); the
-- generated Rust checks child results in the parent (consumer position).
-- Same checks, same first Break, values equal via val ∘ chk = id — the
-- one-edge shift is not observable in any fold output.

module AbsorbEnv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

data E : Set where
  lit   : ℕ → E
  add   : E → E → E
  scope : E → E                     -- the binder edge

data EF (X : Set) : Set where
  litL   : ℕ → EF X
  addL   : X → X → EF X
  scopeL : X → EF X

Alg : Set → Set
Alg B = ℕ → EF B → B                -- reduce reads the depth

-- strict env-threaded fold (the Part-I discipline, single-sorted)
foldE : ∀ {B} → Alg B → ℕ → E → B × ℕ
foldE a d (lit n)   = a d (litL n) , d
foldE a d (add x y) =
  let px = foldE a d x
      py = foldE a (proj₂ px) y
  in a (proj₂ py) (addL (proj₁ px) (proj₁ py)) , proj₂ py
foldE a d (scope e) =
  let pe = foldE a (suc d) e
  in a d (scopeL (proj₁ pe)) , d    -- restore = the saved d (the Frame)

balE : ∀ {B} (a : Alg B) d e → proj₂ (foldE a d e) ≡ d
balE a d (lit n) = refl
balE a d (add x y)
  rewrite balE a d x | balE a d y = refl
balE a d (scope e) = refl

-- ControlFlow, verbatim
data CF (A : Set) : Set where
  cont : A → CF A
  brk  : A → CF A

val : ∀ {A} → CF A → A
val (cont x) = x
val (brk x)  = x

chk : ∀ {B} → (B → Bool) → B → CF B
chk ab v = if ab v then brk v else cont v

-- chk inversions
chk-brk : ∀ {B} (ab : B → Bool) v {w} → chk ab v ≡ brk w →
          (ab v ≡ true) × (v ≡ w)
chk-brk ab v eq with ab v
chk-brk ab v refl | true = refl , refl

chk-cont : ∀ {B} (ab : B → Bool) v {w} → chk ab v ≡ cont w → v ≡ w
chk-cont ab v eq with ab v
chk-cont ab v refl | false = refl

val-chk : ∀ {B} (ab : B → Bool) v → val (chk ab v) ≡ v
val-chk ab v with ab v
... | true  = refl
... | false = refl

------------------------------------------------------------------------
-- NAIVE driver: Break bubbles past the restore (the trap).
------------------------------------------------------------------------
foldEA : ∀ {B} → (B → Bool) → Alg B → ℕ → E → CF B × ℕ
foldEA ab a d (lit n) = chk ab (a d (litL n)) , d
foldEA ab a d (add x y) with foldEA ab a d x
... | brk v , d₁ = brk v , d₁
... | cont vx , d₁ with foldEA ab a d₁ y
...   | brk v , d₂ = brk v , d₂
...   | cont vy , d₂ = chk ab (a d₂ (addL vx vy)) , d₂
foldEA ab a d (scope e) with foldEA ab a (suc d) e
... | brk v , d₁ = brk v , d₁                 -- LEAK: restore skipped
... | cont ve , d₁ = chk ab (a d (scopeL ve)) , d

-- T-E: the leak, concretely. Absorbing value hit inside a binder.
sumAlg : Alg ℕ
sumAlg d (litL n)   = n
sumAlg d (addL x y) = x
sumAlg d (scopeL x) = x

ab0 : ℕ → Bool
ab0 zero    = true
ab0 (suc _) = false

naive-leaks : ¬ (proj₂ (foldEA ab0 sumAlg 0 (scope (lit 0))) ≡ 0)
naive-leaks ()

------------------------------------------------------------------------
-- GUARDED driver: identical except the bubble path restores (the fix —
-- in Rust, a guard/unwind restoration rather than sequenced ascend).
------------------------------------------------------------------------
foldEG : ∀ {B} → (B → Bool) → Alg B → ℕ → E → CF B × ℕ
foldEG ab a d (lit n) = chk ab (a d (litL n)) , d
foldEG ab a d (add x y) with foldEG ab a d x
... | brk v , d₁ = brk v , d₁
... | cont vx , d₁ with foldEG ab a d₁ y
...   | brk v , d₂ = brk v , d₂
...   | cont vy , d₂ = chk ab (a d₂ (addL vx vy)) , d₂
foldEG ab a d (scope e) with foldEG ab a (suc d) e
... | brk v , d₁ = brk v , d       -- restore on the unwind path
... | cont ve , d₁ = chk ab (a d (scopeL ve)) , d

-- T-F: guarded balance, every path.
balG : ∀ {B} (ab : B → Bool) (a : Alg B) d e →
       proj₂ (foldEG ab a d e) ≡ d
balG ab a d (lit n) = refl
balG ab a d (add x y) with foldEG ab a d x in eqx
... | brk v , d₁ = trans (cong proj₂ (sym eqx)) (balG ab a d x)
... | cont vx , d₁ with foldEG ab a d₁ y in eqy
...   | brk v , d₂ =
        trans (cong proj₂ (sym eqy))
              (trans (balG ab a d₁ y)
                     (trans (cong proj₂ (sym eqx)) (balG ab a d x)))
...   | cont vy , d₂ =
        trans (cong proj₂ (sym eqy))
              (trans (balG ab a d₁ y)
                     (trans (cong proj₂ (sym eqx)) (balG ab a d x)))
balG ab a d (scope e) with foldEG ab a (suc d) e
... | brk v , d₁  = refl
... | cont ve , d₁ = refl

-- every Break value is absorbing (Breaks are born at chk)
brkAb : ∀ {B} (ab : B → Bool) (a : Alg B) d e {v d'} →
        foldEG ab a d e ≡ (brk v , d') → ab v ≡ true
brkAb ab a d (lit n) eq =
  let (t , ve) = chk-brk ab (a d (litL n)) (cong proj₁ eq)
  in subst (λ z → ab z ≡ true) ve t
brkAb ab a d (add x y) eq with foldEG ab a d x in eqx
... | brk v , d₁ =
        subst (λ z → ab z ≡ true)
              (cong (λ p → val (proj₁ p)) eq)
              (brkAb ab a d x eqx)
... | cont vx , d₁ with foldEG ab a d₁ y in eqy
...   | brk v , d₂ =
          subst (λ z → ab z ≡ true)
                (cong (λ p → val (proj₁ p)) eq)
                (brkAb ab a d₁ y eqy)
...   | cont vy , d₂ =
          let (t , ve) = chk-brk ab (a d₂ (addL vx vy)) (cong proj₁ eq)
          in subst (λ z → ab z ≡ true) ve t
brkAb ab a d (scope e) eq with foldEG ab a (suc d) e in eqe
... | brk v , d₁ =
        subst (λ z → ab z ≡ true)
              (cong (λ p → val (proj₁ p)) eq)
              (brkAb ab a (suc d) e eqe)
... | cont ve , d₁ =
        let (t , veq) = chk-brk ab (a d (scopeL ve)) (cong proj₁ eq)
        in subst (λ z → ab z ≡ true) veq t

-- per-context annihilation (as documented on FoldAlg::absorbing)
record Ann {B : Set} (ab : B → Bool) (a : Alg B) : Set where
  field
    addA : ∀ d x y → ab x ≡ true → a d (addL x y) ≡ x
    addB : ∀ d x y → ab y ≡ true → a d (addL x y) ≡ y
    sco  : ∀ d x   → ab x ≡ true → a d (scopeL x) ≡ x
open Ann

-- T-G: guarded short-circuiting fold agrees with the strict fold.
agree : ∀ {B} (ab : B → Bool) (a : Alg B) → Ann ab a →
        ∀ d e → val (proj₁ (foldEG ab a d e)) ≡ proj₁ (foldE a d e)
agree ab a ann d (lit n) = val-chk ab (a d (litL n))
agree ab a ann d (add x y) with foldEG ab a d x in eqx
... | brk v , d₁ rewrite balE a d x =
      let vx≡ : v ≡ proj₁ (foldE a d x)
          vx≡ = trans (cong (λ p → val (proj₁ p)) (sym eqx)) (agree ab a ann d x)
          abx = subst (λ z → ab z ≡ true) vx≡ (brkAb ab a d x eqx)
      in trans vx≡
               (sym (addA ann (proj₂ (foldE a d y))
                          (proj₁ (foldE a d x)) (proj₁ (foldE a d y)) abx))
... | cont vx , d₁ with foldEG ab a d₁ y in eqy
...   | brk v , d₂ rewrite balE a d x =
        let d₁≡d : d₁ ≡ d
            d₁≡d = trans (cong proj₂ (sym eqx)) (balG ab a d x)
            vy≡ : v ≡ proj₁ (foldE a d y)
            vy≡ = trans (trans (cong (λ p → val (proj₁ p)) (sym eqy))
                               (agree ab a ann d₁ y))
                        (cong (λ dd → proj₁ (foldE a dd y)) d₁≡d)
            aby = subst (λ z → ab z ≡ true) vy≡ (brkAb ab a d₁ y eqy)
        in trans vy≡
                 (sym (addB ann (proj₂ (foldE a d y))
                            (proj₁ (foldE a d x)) (proj₁ (foldE a d y)) aby))
...   | cont vy , d₂
        rewrite balE a d x
              | trans (cong proj₂ (sym eqy))
                      (trans (balG ab a d₁ y)
                             (trans (cong proj₂ (sym eqx)) (balG ab a d x)))
        = let d₁≡d : d₁ ≡ d
              d₁≡d = trans (cong proj₂ (sym eqx)) (balG ab a d x)
              vx≡ : vx ≡ proj₁ (foldE a d x)
              vx≡ = trans (cong (λ p → val (proj₁ p)) (sym eqx)) (agree ab a ann d x)
              vy≡ : vy ≡ proj₁ (foldE a d y)
              vy≡ = trans (trans (cong (λ p → val (proj₁ p)) (sym eqy))
                                 (agree ab a ann d₁ y))
                          (cong (λ dd → proj₁ (foldE a dd y)) d₁≡d)
          in trans (val-chk ab (a d (addL vx vy)))
                   (trans (cong₂ (λ u w → a d (addL u w)) vx≡ vy≡)
                          (cong (λ dd → a dd (addL (proj₁ (foldE a d x))
                                                   (proj₁ (foldE a d y))))
                                (sym (balE a d y))))
agree ab a ann d (scope e) with foldEG ab a (suc d) e in eqe
... | brk v , d₁ =
      let ve≡ : v ≡ proj₁ (foldE a (suc d) e)
          ve≡ = trans (cong (λ p → val (proj₁ p)) (sym eqe)) (agree ab a ann (suc d) e)
          abe : ab (proj₁ (foldE a (suc d) e)) ≡ true
          abe = subst (λ z → ab z ≡ true) ve≡ (brkAb ab a (suc d) e eqe)
      in trans ve≡ (sym (sco ann d (proj₁ (foldE a (suc d) e)) abe))
... | cont ve , d₁ =
      let ve≡ = trans (cong (λ p → val (proj₁ p)) (sym eqe)) (agree ab a ann (suc d) e)
      in trans (val-chk ab (a d (scopeL ve)))
               (cong (λ u → a d (scopeL u)) ve≡)
