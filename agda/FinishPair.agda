{-# OPTIONS --safe #-}
-- The finish-grade banana split — the law behind `accumulate_finish`.
-- An accumulator here is (S, step, s₀) with an eliminator fin : S → O;
-- creature_feature's `Accumulates` is exactly this shape, and its
-- N-seed min-sketch is a shipped customer with State ≠ Output (the
-- {seeds, mins} record finishes into the hash array), so the eliminator
-- grade is forced by a real instance, not invented.
--
--   T-S  split        : the paired accumulator (componentwise step)
--        computes both folds in one pass.
--   T-F  finish-split : one fused pass THROUGH the eliminators equals
--        two independent passes — featurize_x2 at the finish grade.
--
-- The proof shape is itself the finding: T-F is one `cong` past T-S.
-- `finish` is a post-map and imposes NO new algebraic obligation on the
-- pairing — which is why the Rust surface can take it as a bare
-- `FnOnce(State) -> A` closure rather than a lawful trait.

module FinishPair where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

module _ {A S T O P : Set}
         (stepS : S → A → S) (s₀ : S) (finS : S → O)
         (stepT : T → A → T) (t₀ : T) (finT : T → P) where

  -- newest-first histories, as in GapClock: the head is the last token
  foldS : List A → S
  foldS []      = s₀
  foldS (x ∷ h) = stepS (foldS h) x

  foldT : List A → T
  foldT []      = t₀
  foldT (x ∷ h) = stepT (foldT h) x

  -- the paired accumulator: both components step on every token
  step× : (S × T) → A → (S × T)
  step× (s , t) x = stepS s x , stepT t x

  fold× : List A → S × T
  fold× []      = s₀ , t₀
  fold× (x ∷ h) = step× (fold× h) x

  -- T-S
  split : ∀ h → fold× h ≡ (foldS h , foldT h)
  split []      = refl
  split (x ∷ h) = cong (λ p → step× p x) (split h)

  fin× : S × T → O × P
  fin× (s , t) = finS s , finT t

  -- T-F
  finish-split : ∀ h → fin× (fold× h) ≡ (finS (foldS h) , finT (foldT h))
  finish-split h = cong fin× (split h)
