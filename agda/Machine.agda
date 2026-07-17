{-# OPTIONS --safe #-}
-- The FoldMachine correctness theorem — SECOND statement. The first
-- version of this file proved a postfix, env-free machine: green, true,
-- and NOT the machine in cata.rs (rim audit finding). The shipped
-- machine is bracketed (Open/Leaf/Close) and carries `depth` — it is
-- the SCOPED fold defunctionalized: Open enters a scope, Leaf reduces
-- reading the depth, Close reduces the node and exits. This file proves
-- that machine, for any depth-reading leaf algebra and node algebra:
--
--   T-M  machine≡fold : running the token stream of `t` from (d , s)
--        returns (d , foldE d t ∷ s) — depth balanced, fold on top —
--        so the Rust readout condition (open ≡ 0, stack a singleton)
--        holds at the end of a well-formed stream with the fold inside.

module Machine where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

data Tree : Set where
  leaf : ℕ → Tree
  node : Tree → Tree → Tree

-- the env-reading (scoped) fold the machine implements
module M {B : Set} (aL : ℕ → ℕ → B) (aN : ℕ → B → B → B) where

  foldE : ℕ → Tree → B
  foldE d (leaf p)   = aL d p
  foldE d (node a b) = aN d (foldE (suc d) a) (foldE (suc d) b)

  data Tok : Set where
    open̂  : Tok
    leaf̂  : ℕ → Tok
    close : Tok

  -- pre-order brackets: Open, children, Close (cata.rs `tokenize`)
  toks : Tree → List Tok
  toks (leaf p)   = leaf̂ p ∷ []
  toks (node a b) = open̂ ∷ toks a ++ toks b ++ close ∷ []

  St : Set
  St = ℕ × List B

  -- the machine: depth-carrying, stack-reducing (cata.rs `update`);
  -- Close pops b then a (right on top), reduces at the DECREMENTED
  -- depth, exactly as shipped. Underflow wedges (self-loop) — never
  -- reached on `toks` output, which the theorem makes precise.
  runM : List Tok → St → St
  runM [] st = st
  runM (open̂ ∷ k)  (d , s)         = runM k (suc d , s)
  runM (leaf̂ p ∷ k) (d , s)         = runM k (d , aL d p ∷ s)
  runM (close ∷ k) (suc d , b ∷ a ∷ s) = runM k (d , aN d a b ∷ s)
  runM (close ∷ k) st = st -- wedged

  -- the continuation lemma: a subtree's tokens push its fold and
  -- restore the depth — balance and value in one statement
  key : ∀ t k d s → runM (toks t ++ k) (d , s) ≡ runM k (d , foldE d t ∷ s)
  key (leaf p) k d s = refl
  key (node a b) k d s
    rewrite ++-assoc (toks a) (toks b ++ close ∷ []) k
          | key a ((toks b ++ close ∷ []) ++ k) (suc d) s
          | ++-assoc (toks b) (close ∷ []) k
          | key b (close ∷ k) (suc d) (foldE (suc d) a ∷ s)
    = refl

  -- T-M: from the initial state, the machine halts balanced at depth 0
  -- with exactly the fold on the stack — the Rust readout's condition
  machine≡fold : ∀ t → runM (toks t) (0 , []) ≡ (0 , foldE 0 t ∷ [])
  machine≡fold t
    rewrite sym (++-identityʳ (toks t)) = key t [] 0 []
