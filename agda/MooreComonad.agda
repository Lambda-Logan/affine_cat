{-# OPTIONS --safe --cubical --guardedness #-}
-- Moore = the cofree-comonoid comonad. This is the module the whole
-- categorical frame rests on, and it is the one place the corpus needs
-- CUBICAL: the comonad laws are equalities between COINDUCTIVE machines,
-- and proving those without cubical needs a hand-rolled bisimulation
-- plus a postulated coinduction principle. Cubical supplies coinductive
-- extensionality directly — copattern the proof into a path — so the
-- laws are provable on the nose. Cubical is used HERE and nowhere else.
--
-- A Moore machine over input A, output B is the terminal coalgebra
-- Moore A B ≅ B × (A → Moore A B): a readout `ν` and a transition `δ`.
-- Fixing A, `Moore A` is an endofunctor on B, and it is a comonad — the
-- cofree comonoid on the input. Its structure maps:
--   ε = ν            (extract / counit)         Fn(&S) → B  in the crate
--   dup              (duplicate / comultiply)   relabel each state by its
--                                               own subtree.
--
--   T1  ε∘dup = id            (left counit)          — refl
--   T2  (map ε)∘dup = id      (right counit)         — cubical coind.
--   T3  dup∘dup = (map dup)∘dup  (coassociativity)   — cubical coind.
--   T-SCAN  the running readout ("scan", the combinator the frame
--           PREDICTS the crate is missing) falls out of dup: the readout
--           of `dup m` after any history is the submachine reached, whose
--           ε is the readout of `m` there.
--
-- Seam (named): this proves the COMONAD LAWS in Set, not the universal
-- property (freeness/cofreeness) — that needs an abstract setting. The
-- frame's "cofree" is the design reading; what is mechanized is that the
-- three comonad equations hold exactly.

module MooreComonad where

open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

private variable A B C D : Set

-- minimal cubical toolkit (no external library)
refl : {x : A} → x ≡ x
refl {x = x} _ = x

------------------------------------------------------------------------
-- The machine (coinductive).
------------------------------------------------------------------------
record Moore (A B : Set) : Set where
  coinductive
  field
    ν : B                 -- readout / extract
    δ : A → Moore A B     -- transition
open Moore

-- functor action on the output
mmap : (B → C) → Moore A B → Moore A C
ν (mmap f m)   = f (ν m)
δ (mmap f m) a = mmap f (δ m a)

-- comonad structure
ε : Moore A B → B
ε = ν

dup : Moore A B → Moore A (Moore A B)
ν (dup m)   = m
δ (dup m) a = dup (δ m a)

------------------------------------------------------------------------
-- T1 : ε ∘ dup ≡ id.  ν (dup m) = m definitionally.
------------------------------------------------------------------------
counit-l : (m : Moore A B) → ε (dup m) ≡ m
counit-l m = refl

------------------------------------------------------------------------
-- T2 : (mmap ε) ∘ dup ≡ id.  Coinductive: copattern into the path.
--   ν side: ν (mmap ε (dup m)) = ε (ν (dup m)) = ε m = ν m   (const path)
--   δ side: reduces to the same law at (δ m a)               (corecursion)
------------------------------------------------------------------------
counit-r : (m : Moore A B) → mmap ε (dup m) ≡ m
ν (counit-r m i)   = ν m
δ (counit-r m i) a = counit-r (δ m a) i

------------------------------------------------------------------------
-- T3 : dup ∘ dup ≡ (mmap dup) ∘ dup  (coassociativity).
--   ν side: both reduce to `dup m`                           (const path)
--   δ side: reduces to the same law at (δ m a)               (corecursion)
------------------------------------------------------------------------
coassoc : (m : Moore A B) → dup (dup m) ≡ mmap dup (dup m)
ν (coassoc m i)   = dup m
δ (coassoc m i) a = coassoc (δ m a) i

------------------------------------------------------------------------
-- T-SCAN : the predicted combinator. Feeding inputs = following δ; the
-- readout of the DUPLICATED machine after a history is exactly the
-- submachine `m` reaches, so ε of it is m's readout at that prefix. This
-- is `scan` (running fold): all intermediate readouts, and it is a
-- COROLLARY of dup, not a new primitive.
------------------------------------------------------------------------
run : Moore A B → List A → Moore A B
run m []       = m
run m (a ∷ as) = run (δ m a) as

-- the readout of `dup m` after `as` is the machine `m` reaches after `as`
dup-tracks : (m : Moore A B)(as : List A) → ν (run (dup m) as) ≡ run m as
dup-tracks m []       = refl
dup-tracks m (a ∷ as) = dup-tracks (δ m a) as

-- hence ε ∘ (readout of dup) = readout of m at that point: scan is dup+ε
scan : Moore A B → List A → List B
scan m []       = ν m ∷ []
scan m (a ∷ as) = ν m ∷ scan (δ m a) as

-- The readout of the dup-orbit, post-composed with ε, is m's readout at
-- that point: scan is the ε-image of the dup orbit. `ε (run (dup m) as)`
-- is a machine (the submachine); applying ν gives its readout, which
-- equals m's readout after `as`.
scan-last : (m : Moore A B)(as : List A) → ν (ε (run (dup m) as)) ≡ ν (run m as)
scan-last m as i = ν (dup-tracks m as i)
