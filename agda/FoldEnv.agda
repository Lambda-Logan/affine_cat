{-# OPTIONS --safe #-}
-- Witness corpus for the affine-cat `cata` design discussion.
-- Agda 2.6.3, agda-stdlib 1.7.3, --safe, no postulates.
--
-- The driver is the State monad written out: Ctx → (B × Ctx). Threading it
-- concretely (rather than via the stdlib monad instance) keeps every proof a
-- plain `rewrite`; the denotation is identical. Cubical is not needed: all
-- equalities are proved pointwise (applied at a context), so no funext.

-- Transport note (standing seam): this corpus models OWNED strict
-- payloads; the shipped Rust lends payloads by reference (Layer<'a>).
-- No theorem here is payload-load-bearing — values flow through holes,
-- payloads only into reduces — so the transport is shape-preserving,
-- asserted rather than re-proved. If a future theorem quantifies over
-- payload identity, re-derive it against a borrowed model first.
module FoldEnv where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (m+n∸n≡m)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------
-- Contexts: a stack of frames; frame = the column ids a binder introduces.
------------------------------------------------------------------------

Frame : Set
Frame = List ℕ

Ctx : Set
Ctx = List Frame

-- total lookups with default (extrinsic scoping, as in the Rust IR)
nthF : ℕ → Ctx → Frame
nthF _       []      = []
nthF zero    (f ∷ _) = f
nthF (suc d) (_ ∷ Γ) = nthF d Γ

nthN : ℕ → Frame → ℕ
nthN _       []       = 0
nthN zero    (x ∷ _)  = x
nthN (suc i) (_ ∷ xs) = nthN i xs

-- de Bruijn: depth 0 = innermost scope = head of the stack
resolveVar : Ctx → ℕ → ℕ → ℕ
resolveVar Γ d i = nthN i (nthF d Γ)

------------------------------------------------------------------------
-- The two-sorted IR (mutual): the binder edge is exists : Rel → Val,
-- and a Rel's table introduces the frame its Filter predicate sees.
------------------------------------------------------------------------

data Val : Set
data Rel : Set

data Val where
  col    : ℕ → ℕ → Val
  lit    : ℕ → Val
  add    : Val → Val → Val
  exists : Rel → Val

data Rel where
  table : Frame → Rel
  filtr : Rel → Val → Rel

-- pattern functors: two sorts, two holes each (endofunctor on Set × Set)
data ValLayer (V R : Set) : Set where
  colL    : ℕ → ℕ → ValLayer V R
  litL    : ℕ → ValLayer V R
  addL    : V → V → ValLayer V R
  existsL : R → ValLayer V R

data RelLayer (V R : Set) : Set where
  tableL : Frame → RelLayer V R
  filtrL : R → V → RelLayer V R

------------------------------------------------------------------------
-- The two-phase design, pure form.  KEY ARCHITECTURAL CHOICE exposed by
-- this formalization: the DRIVER owns all context motion (push at table,
-- restore at exists); the algebra only READS the context in `reduce`.
-- The algebra of the Rust prototype instead owned `enter_columns` — see
-- theorem `banana` below for why that was a latent bug.
------------------------------------------------------------------------

record Alg (V R : Set) : Set where
  field
    reduceV : Ctx → ValLayer V R → V
    reduceR : Ctx → RelLayer V R → R
open Alg public

-- restore-to-height: the affine Frame (saved height) instead of a snapshot
trunc : ℕ → Ctx → Ctx
trunc h Γ = drop (length Γ ∸ h) Γ

foldV : ∀ {V R} → Alg V R → Ctx → Val → V × Ctx
foldR : ∀ {V R} → Alg V R → Ctx → Rel → R × Ctx

foldV a Γ (col d i) = reduceV a Γ (colL d i) , Γ
foldV a Γ (lit n)   = reduceV a Γ (litL n)   , Γ
foldV a Γ (add x y) =
  reduceV a Γ₂ (addL (proj₁ px) (proj₁ py)) , Γ₂
  where
    px = foldV a Γ x
    py = foldV a (proj₂ px) y
    Γ₂ = proj₂ py
foldV a Γ (exists r) =                          -- the binder edge:
  reduceV a Γ' (existsL (proj₁ pr)) , Γ'        --   descend = remember height
  where                                         --   ascend  = trunc, ONCE, here
    pr = foldR a Γ r
    Γ' = trunc (length Γ) (proj₂ pr)
foldR a Γ (table f) = reduceR a (f ∷ Γ) (tableL f) , (f ∷ Γ)   -- driver pushes
foldR a Γ (filtr r p) =
  reduceR a Γ₂ (filtrL (proj₁ pr) (proj₁ pp)) , Γ₂
  where
    pr = foldR a Γ r
    pp = foldV a (proj₂ pr) p    -- predicate folded in the table's scope
    Γ₂ = proj₂ pp

------------------------------------------------------------------------
-- THEOREM 1 (balance): context evolution is a function of the term alone,
-- for EVERY algebra.  Val-folds restore the context exactly; Rel-folds
-- extend it by precisely the frames the relation binds.  In the Rust
-- design this was "by construction" via the moved Frame; here it is a
-- theorem because pure `reduce` cannot touch the context at all.
------------------------------------------------------------------------

binds : Rel → Ctx
binds (table f)   = f ∷ []
binds (filtr r _) = binds r

-- drop (length xs) (xs ++ ys) ≡ ys
drop-prefix : ∀ (xs ys : Ctx) → drop (length xs) (xs ++ ys) ≡ ys
drop-prefix []       ys = refl
drop-prefix (x ∷ xs) ys = drop-prefix xs ys

trunc-++ : ∀ (b Γ : Ctx) → trunc (length Γ) (b ++ Γ) ≡ Γ
trunc-++ b Γ = begin
  drop (length (b ++ Γ) ∸ length Γ) (b ++ Γ)
    ≡⟨ cong (λ n → drop (n ∸ length Γ) (b ++ Γ)) (length-++ b) ⟩
  drop (length b + length Γ ∸ length Γ) (b ++ Γ)
    ≡⟨ cong (λ n → drop n (b ++ Γ)) (m+n∸n≡m (length b) (length Γ)) ⟩
  drop (length b) (b ++ Γ)
    ≡⟨ drop-prefix b Γ ⟩
  Γ ∎

balV : ∀ {V R} (a : Alg V R) Γ e → proj₂ (foldV a Γ e) ≡ Γ
balR : ∀ {V R} (a : Alg V R) Γ r → proj₂ (foldR a Γ r) ≡ binds r ++ Γ

balV a Γ (col d i) = refl
balV a Γ (lit n)   = refl
balV a Γ (add x y)
  rewrite balV a Γ x | balV a Γ y = refl
balV a Γ (exists r)
  rewrite balR a Γ r = trunc-++ (binds r) Γ
balR a Γ (table f)   = refl
balR a Γ (filtr r p)
  rewrite balR a Γ r | balV a (binds r ++ Γ) p = refl

------------------------------------------------------------------------
-- The concrete pass: resolution (collect the globally-resolved column id
-- of every variable).  Genuinely context-dependent at each col.
------------------------------------------------------------------------

resolveAlg : Alg (List ℕ) (List ℕ)
reduceV resolveAlg Γ (colL d i)  = resolveVar Γ d i ∷ []
reduceV resolveAlg Γ (litL _)    = []
reduceV resolveAlg Γ (addL x y)  = x ++ y
reduceV resolveAlg Γ (existsL r) = r
reduceR resolveAlg Γ (tableL _)  = []
reduceR resolveAlg Γ (filtrL r p) = r ++ p

------------------------------------------------------------------------
-- THEOREM 2 (the convergence claim): the env-threaded two-phase fold IS a
-- PLAIN catamorphism at the exponential carrier — Milewski's Env→B, per
-- sort; the Rel sort's carrier must also EXPOSE its context delta
-- (inherited + synthesized = the lens, per Spivak).  Note the driver
-- below has no Ctx anywhere: the context lives only in the carriers.
------------------------------------------------------------------------

cataV : ∀ {V R} → (ValLayer V R → V) → (RelLayer V R → R) → Val → V
cataR : ∀ {V R} → (ValLayer V R → V) → (RelLayer V R → R) → Rel → R

cataV fv fr (col d i) = fv (colL d i)
cataV fv fr (lit n)   = fv (litL n)
cataV fv fr (add x y) = fv (addL (cataV fv fr x) (cataV fv fr y))
cataV fv fr (exists r) = fv (existsL (cataR fv fr r))
cataR fv fr (table f)   = fr (tableL f)
cataR fv fr (filtr r p) = fr (filtrL (cataR fv fr r) (cataV fv fr p))

-- exponential carriers: V† = Ctx → List ℕ ;  R† = Ctx → List ℕ × Ctx
V† R† : Set
V† = Ctx → List ℕ
R† = Ctx → List ℕ × Ctx

algV† : ValLayer V† R† → V†
algV† (colL d i)  Γ = resolveVar Γ d i ∷ []
algV† (litL _)    Γ = []
algV† (addL f g)  Γ = f Γ ++ g Γ
algV† (existsL h) Γ = proj₁ (h Γ)            -- restore = ignore the delta

algR† : RelLayer V† R† → R†
algR† (tableL f)   Γ = [] , (f ∷ Γ)
algR† (filtrL h g) Γ = (proj₁ (h Γ) ++ g (proj₂ (h Γ))) , proj₂ (h Γ)

readerV : Val → V†
readerV = cataV algV† algR†
readerR : Rel → R†
readerR = cataR algV† algR†

-- pointwise agreement (hence no funext, hence no cubical needed)
agreeV : ∀ e Γ → proj₁ (foldV resolveAlg Γ e) ≡ readerV e Γ
agreeR : ∀ r Γ → foldR resolveAlg Γ r ≡ readerR r Γ

agreeV (col d i) Γ = refl
agreeV (lit n)   Γ = refl
agreeV (add x y) Γ
  rewrite balV resolveAlg Γ x
        | agreeV x Γ | agreeV y Γ = refl
agreeV (exists r) Γ
  rewrite agreeR r Γ = refl
agreeR (table f) Γ = refl
agreeR (filtr r p) Γ
  rewrite agreeR r Γ
        | balV resolveAlg (proj₂ (readerR r Γ)) p
        | agreeV p (proj₂ (readerR r Γ)) = refl

------------------------------------------------------------------------
-- THEOREM 3 (the letter's shape, made precise): a driver for the
-- letter's algebra type — env in, FOLDED-children layer in, out + env
-- out — hands every exists-subtree the PARENT-ENTRY context, for every
-- algebra.  `blind` is definitional (refl): the driver has no edge at
-- which any algebra could run before the descent.  So context-sensitive
-- resolution under a binder is expressible only by enriching B with the
-- context — and Theorem 2 shows that enrichment is exactly the
-- exponential carrier, i.e. what the two-phase API defunctionalizes.
------------------------------------------------------------------------

record LetterAlg (B : Set) : Set where
  field
    stepV : Ctx → ValLayer B B → B × Ctx
    stepR : Ctx → RelLayer B B → B × Ctx
open LetterAlg

letterV : ∀ {B} → LetterAlg B → Ctx → Val → B × Ctx
letterR : ∀ {B} → LetterAlg B → Ctx → Rel → B × Ctx

letterV a Γ (col d i) = stepV a Γ (colL d i)
letterV a Γ (lit n)   = stepV a Γ (litL n)
letterV a Γ (add x y) =
  stepV a (proj₂ py) (addL (proj₁ px) (proj₁ py))
  where
    px = letterV a Γ x
    py = letterV a (proj₂ px) y
letterV a Γ (exists r) =
  stepV a (proj₂ pr) (existsL (proj₁ pr))
  where
    pr = letterR a Γ r          -- ← subtree folded at Γ, unmodified
letterR a Γ (table f)   = stepR a Γ (tableL f)
letterR a Γ (filtr r p) =
  stepR a (proj₂ pp) (filtrL (proj₁ pr) (proj₁ pp))
  where
    pr = letterR a Γ r
    pp = letterV a (proj₂ pr) p

blind : ∀ {B} (a : LetterAlg B) Γ r →
        letterV a Γ (exists r)
          ≡ stepV a (proj₂ (letterR a Γ r)) (existsL (proj₁ (letterR a Γ r)))
blind a Γ r = refl

------------------------------------------------------------------------
-- THEOREM 4 (banana-split is unconditionally sound HERE): one traversal
-- with the product algebra equals two traversals — with no side
-- condition, BECAUSE context motion is driver-owned (Theorem 1: it is
-- algebra-independent).  The Rust prototype put `enter_columns` on the
-- algebra; there, Pair(F,G) duplicates the push and the theorem fails.
-- The unzip below duplicates node payloads — free in cartesian Agda,
-- a Comonoid bound in affine Rust.
------------------------------------------------------------------------

pairAlg : ∀ {V₁ R₁ V₂ R₂} → Alg V₁ R₁ → Alg V₂ R₂ → Alg (V₁ × V₂) (R₁ × R₂)
reduceV (pairAlg a b) Γ (colL d i)  = reduceV a Γ (colL d i) , reduceV b Γ (colL d i)
reduceV (pairAlg a b) Γ (litL n)    = reduceV a Γ (litL n) , reduceV b Γ (litL n)
reduceV (pairAlg a b) Γ (addL x y)  =
  reduceV a Γ (addL (proj₁ x) (proj₁ y)) , reduceV b Γ (addL (proj₂ x) (proj₂ y))
reduceV (pairAlg a b) Γ (existsL r) =
  reduceV a Γ (existsL (proj₁ r)) , reduceV b Γ (existsL (proj₂ r))
reduceR (pairAlg a b) Γ (tableL f)   = reduceR a Γ (tableL f) , reduceR b Γ (tableL f)
reduceR (pairAlg a b) Γ (filtrL r p) =
  reduceR a Γ (filtrL (proj₁ r) (proj₁ p)) , reduceR b Γ (filtrL (proj₂ r) (proj₂ p))

bananaV : ∀ {V₁ R₁ V₂ R₂} (a : Alg V₁ R₁) (b : Alg V₂ R₂) Γ e →
          proj₁ (foldV (pairAlg a b) Γ e)
            ≡ (proj₁ (foldV a Γ e) , proj₁ (foldV b Γ e))
bananaR : ∀ {V₁ R₁ V₂ R₂} (a : Alg V₁ R₁) (b : Alg V₂ R₂) Γ r →
          proj₁ (foldR (pairAlg a b) Γ r)
            ≡ (proj₁ (foldR a Γ r) , proj₁ (foldR b Γ r))

bananaV a b Γ (col d i) = refl
bananaV a b Γ (lit n)   = refl
bananaV a b Γ (add x y)
  rewrite balV (pairAlg a b) Γ x | balV a Γ x | balV b Γ x
        | balV (pairAlg a b) Γ y | balV a Γ y | balV b Γ y
        | bananaV a b Γ x | bananaV a b Γ y = refl
bananaV a b Γ (exists r)
  rewrite balR (pairAlg a b) Γ r | balR a Γ r | balR b Γ r
        | bananaR a b Γ r = refl
bananaR a b Γ (table f) = refl
bananaR a b Γ (filtr r p)
  rewrite balR (pairAlg a b) Γ r | balR a Γ r | balR b Γ r
        | balV (pairAlg a b) (binds r ++ Γ) p
        | balV a (binds r ++ Γ) p | balV b (binds r ++ Γ) p
        | bananaR a b Γ r | bananaV a b (binds r ++ Γ) p = refl

------------------------------------------------------------------------
-- The running example from the Rust prototype, now with a PROVED answer:
-- outer table binds [a=10,b=11]; subquery table binds [x=20];
-- Col(depth 1, idx 0) inside the subquery must reach the OUTER a=10.
------------------------------------------------------------------------

example : Rel
example =
  filtr (table (10 ∷ 11 ∷ []))
        (add (col 0 0)
             (exists (filtr (table (20 ∷ []))
                            (add (col 0 0) (col 1 0)))))

example-resolves : proj₁ (foldR resolveAlg [] example) ≡ 10 ∷ 20 ∷ 10 ∷ []
example-resolves = refl

example-balanced : proj₂ (foldR resolveAlg [] example) ≡ (10 ∷ 11 ∷ []) ∷ []
example-balanced = refl

------------------------------------------------------------------------
-- PART II: the mutating-reduce model (State carrier for the algebra
-- itself), closing the gap flagged in the fork pass: the Rust design
-- gives `reduce` access to `&mut Env`; the theorems above assume it
-- cannot.  Below: (a) balance FAILS in general — counterexample;
-- (b) sequential Pair is POISONED — F's mutations leak into G's reads,
-- counterexample; (c) the positive law: context-silent algebras
-- collapse to the pure model, recovering every Part-I theorem.
------------------------------------------------------------------------

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

record AlgS (V R : Set) : Set where
  field
    reduceVS : Ctx → ValLayer V R → V × Ctx
    reduceRS : Ctx → RelLayer V R → R × Ctx
open AlgS public

foldVS : ∀ {V R} → AlgS V R → Ctx → Val → V × Ctx
foldRS : ∀ {V R} → AlgS V R → Ctx → Rel → R × Ctx

foldVS a Γ (col d i) = reduceVS a Γ (colL d i)
foldVS a Γ (lit n)   = reduceVS a Γ (litL n)
foldVS a Γ (add x y) =
  reduceVS a (proj₂ py) (addL (proj₁ px) (proj₁ py))
  where
    px = foldVS a Γ x
    py = foldVS a (proj₂ px) y
foldVS a Γ (exists r) =
  reduceVS a (trunc (length Γ) (proj₂ pr)) (existsL (proj₁ pr))
  where
    pr = foldRS a Γ r
foldRS a Γ (table f)   = reduceRS a (f ∷ Γ) (tableL f)
foldRS a Γ (filtr r p) =
  reduceRS a (proj₂ pp) (filtrL (proj₁ pr) (proj₁ pp))
  where
    pr = foldRS a Γ r
    pp = foldVS a (proj₂ pr) p

-- (a) BALANCE FAILS: an algebra that pushes a junk frame at every lit.
junk : AlgS ℕ ℕ
reduceVS junk Γ (colL d i)  = resolveVar Γ d i , Γ
reduceVS junk Γ (litL n)    = n , ([] ∷ Γ)          -- the mutation
reduceVS junk Γ (addL x y)  = x + y , Γ
reduceVS junk Γ (existsL r) = r , Γ
reduceRS junk Γ (tableL _)  = 0 , Γ
reduceRS junk Γ (filtrL r p) = r + p , Γ

balance-fails : ¬ (proj₂ (foldVS junk [] (lit 0)) ≡ [])
balance-fails ()

-- (b) PAIR IS POISONED: sequential product of state algebras.
pairS : ∀ {V₁ R₁ V₂ R₂} → AlgS V₁ R₁ → AlgS V₂ R₂ → AlgS (V₁ × V₂) (R₁ × R₂)
reduceVS (pairS a b) Γ (colL d i) =
  let pa = reduceVS a Γ (colL d i)
      pb = reduceVS b (proj₂ pa) (colL d i)
  in (proj₁ pa , proj₁ pb) , proj₂ pb
reduceVS (pairS a b) Γ (litL n) =
  let pa = reduceVS a Γ (litL n)
      pb = reduceVS b (proj₂ pa) (litL n)
  in (proj₁ pa , proj₁ pb) , proj₂ pb
reduceVS (pairS a b) Γ (addL x y) =
  let pa = reduceVS a Γ (addL (proj₁ x) (proj₁ y))
      pb = reduceVS b (proj₂ pa) (addL (proj₂ x) (proj₂ y))
  in (proj₁ pa , proj₁ pb) , proj₂ pb
reduceVS (pairS a b) Γ (existsL r) =
  let pa = reduceVS a Γ (existsL (proj₁ r))
      pb = reduceVS b (proj₂ pa) (existsL (proj₂ r))
  in (proj₁ pa , proj₁ pb) , proj₂ pb
reduceRS (pairS a b) Γ (tableL f) =
  let pa = reduceRS a Γ (tableL f)
      pb = reduceRS b (proj₂ pa) (tableL f)
  in (proj₁ pa , proj₁ pb) , proj₂ pb
reduceRS (pairS a b) Γ (filtrL r p) =
  let pa = reduceRS a Γ (filtrL (proj₁ r) (proj₁ p))
      pb = reduceRS b (proj₂ pa) (filtrL (proj₂ r) (proj₂ p))
  in (proj₁ pa , proj₁ pb) , proj₂ pb

-- resolve as a state algebra (context-silent by construction)
resolveS : AlgS ℕ ℕ
reduceVS resolveS Γ (colL d i)  = resolveVar Γ d i , Γ
reduceVS resolveS Γ (litL n)    = 0 , Γ
reduceVS resolveS Γ (addL x y)  = x + y , Γ
reduceVS resolveS Γ (existsL r) = r , Γ
reduceRS resolveS Γ (tableL _)  = 0 , Γ
reduceRS resolveS Γ (filtrL r p) = r + p , Γ

-- The poisoning term: add (lit 0) (col 0 0) in context [[7]].
-- resolveS alone resolves col 0 0 to 7; paired after junk, the junk
-- frame pushed at the lit shadows the real one and it resolves to 0.
poison : Val
poison = add (lit 0) (col 0 0)

Γ₇ : Ctx
Γ₇ = (7 ∷ []) ∷ []

resolve-alone : proj₁ (foldVS resolveS Γ₇ poison) ≡ 7
resolve-alone = refl

resolve-poisoned : proj₂ (proj₁ (foldVS (pairS junk resolveS) Γ₇ poison)) ≡ 0
resolve-poisoned = refl

pair-not-banana :
  ¬ (proj₂ (proj₁ (foldVS (pairS junk resolveS) Γ₇ poison))
      ≡ proj₁ (foldVS resolveS Γ₇ poison))
pair-not-banana ()

-- (c) THE POSITIVE LAW: context-silence.  A silent state algebra is one
-- whose every reduce returns its input context.  Silent algebras
-- collapse to the pure model — so every Part-I theorem (balance,
-- exponential-carrier agreement, unconditional banana) transports.
record Silent {V R} (a : AlgS V R) : Set where
  field
    silV : ∀ Γ l → proj₂ (reduceVS a Γ l) ≡ Γ
    silR : ∀ Γ l → proj₂ (reduceRS a Γ l) ≡ Γ
open Silent

forget : ∀ {V R} → AlgS V R → Alg V R
reduceV (forget a) Γ l = proj₁ (reduceVS a Γ l)
reduceR (forget a) Γ l = proj₁ (reduceRS a Γ l)

collapseV : ∀ {V R} (a : AlgS V R) (s : Silent a) Γ e →
            foldVS a Γ e ≡ foldV (forget a) Γ e
collapseR : ∀ {V R} (a : AlgS V R) (s : Silent a) Γ r →
            foldRS a Γ r ≡ foldR (forget a) Γ r

collapseV a s Γ (col d i) =
  cong (λ c → proj₁ (reduceVS a Γ (colL d i)) , c) (silV s Γ (colL d i))
collapseV a s Γ (lit n) =
  cong (λ c → proj₁ (reduceVS a Γ (litL n)) , c) (silV s Γ (litL n))
collapseV a s Γ (add x y)
  rewrite collapseV a s Γ x
        | balV (forget a) Γ x
        | collapseV a s Γ y
        | balV (forget a) Γ y =
  cong (λ c → proj₁ (reduceVS a Γ (addL (proj₁ (foldV (forget a) Γ x))
                                        (proj₁ (foldV (forget a) Γ y)))) , c)
       (silV s Γ (addL (proj₁ (foldV (forget a) Γ x))
                       (proj₁ (foldV (forget a) Γ y))))
collapseV a s Γ (exists r)
  rewrite collapseR a s Γ r
        | balR (forget a) Γ r
        | trunc-++ (binds r) Γ =
  cong (λ c → proj₁ (reduceVS a Γ (existsL (proj₁ (foldR (forget a) Γ r)))) , c)
       (silV s Γ (existsL (proj₁ (foldR (forget a) Γ r))))
collapseR a s Γ (table f) =
  cong (λ c → proj₁ (reduceRS a (f ∷ Γ) (tableL f)) , c) (silR s (f ∷ Γ) (tableL f))
collapseR a s Γ (filtr r p)
  rewrite collapseR a s Γ r
        | balR (forget a) Γ r
        | collapseV a s (binds r ++ Γ) p
        | balV (forget a) (binds r ++ Γ) p =
  cong (λ c → proj₁ (reduceRS a (binds r ++ Γ)
                       (filtrL (proj₁ (foldR (forget a) Γ r))
                               (proj₁ (foldV (forget a) (binds r ++ Γ) p)))) , c)
       (silR s (binds r ++ Γ)
             (filtrL (proj₁ (foldR (forget a) Γ r))
                     (proj₁ (foldV (forget a) (binds r ++ Γ) p))))

------------------------------------------------------------------------
-- PART III: the well-scopedness hypothesis, stated and discharged.
-- Part I's resolution theorems use total-with-default lookup: ill-scoped
-- input resolves to junk silently.  Here: the WS predicate (over context
-- SHAPES — frame sizes — so it is static, no values needed), a CHECKED
-- resolver in Maybe, and the theorem: on WS input the checked resolver
-- never fails and agrees with the total one.  This is the hypothesis the
-- earlier theorems implicitly wanted, now explicit.
------------------------------------------------------------------------

open import Data.Nat using (_≤_; s≤s; z≤n; _<_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (map)
open import Data.List.Properties using (map-++-commute)

Shape : Set
Shape = List ℕ

shape : Ctx → Shape
shape = map length

data WSV (sh : Shape) : Val → Set
data WSR (sh : Shape) : Rel → Set

data WSV sh where
  ws-col    : ∀ {d i} → i < nthN d sh → WSV sh (col d i)
  ws-lit    : ∀ {n} → WSV sh (lit n)
  ws-add    : ∀ {x y} → WSV sh x → WSV sh y → WSV sh (add x y)
  ws-exists : ∀ {r} → WSR sh r → WSV sh (exists r)

data WSR sh where
  ws-table : ∀ {f} → WSR sh (table f)
  ws-filtr : ∀ {r p} → WSR sh r → WSV (shape (binds r) ++ sh) p →
             WSR sh (filtr r p)

-- checked lookups
nthN? : ℕ → Frame → Maybe ℕ
nthN? _       []       = nothing
nthN? zero    (x ∷ _)  = just x
nthN? (suc i) (_ ∷ xs) = nthN? i xs

nthF? : ℕ → Ctx → Maybe Frame
nthF? _       []      = nothing
nthF? zero    (f ∷ _) = just f
nthF? (suc d) (_ ∷ Γ) = nthF? d Γ

resolveVar? : Ctx → ℕ → ℕ → Maybe ℕ
resolveVar? Γ d i with nthF? d Γ
... | nothing = nothing
... | just f  = nthN? i f

-- in-bounds lookups don't fail and agree with the defaults
nthN?-just : ∀ i xs → i < length xs → nthN? i xs ≡ just (nthN i xs)
nthN?-just zero    (x ∷ _)  _         = refl
nthN?-just (suc i) (_ ∷ xs) (s≤s lt)  = nthN?-just i xs lt

resolveVar?-just : ∀ Γ d i → i < nthN d (shape Γ) →
                   resolveVar? Γ d i ≡ just (resolveVar Γ d i)
resolveVar?-just []      zero    i ()
resolveVar?-just []      (suc d) i ()
resolveVar?-just (f ∷ Γ) zero    i lt = nthN?-just i f lt
resolveVar?-just (f ∷ Γ) (suc d) i lt = resolveVar?-just Γ d i lt

-- checked resolution as a (pure, context-silent) algebra in Maybe
_⊞_ : Maybe (List ℕ) → Maybe (List ℕ) → Maybe (List ℕ)
just xs ⊞ just ys = just (xs ++ ys)
just _  ⊞ nothing = nothing
nothing ⊞ _       = nothing

single? : Maybe ℕ → Maybe (List ℕ)
single? (just n) = just (n ∷ [])
single? nothing  = nothing

resolve?Alg : Alg (Maybe (List ℕ)) (Maybe (List ℕ))
reduceV resolve?Alg Γ (colL d i)  = single? (resolveVar? Γ d i)
reduceV resolve?Alg Γ (litL _)    = just []
reduceV resolve?Alg Γ (addL x y)  = x ⊞ y
reduceV resolve?Alg Γ (existsL r) = r
reduceR resolve?Alg Γ (tableL _)  = just []
reduceR resolve?Alg Γ (filtrL r p) = r ⊞ p

-- THE THEOREM: well-scoped terms never hit the default; the checked and
-- total resolvers agree.  (The context/shape alignment rides on balance.)
safeV : ∀ {e} Γ → WSV (shape Γ) e →
        proj₁ (foldV resolve?Alg Γ e) ≡ just (proj₁ (foldV resolveAlg Γ e))
safeR : ∀ {r} Γ → WSR (shape Γ) r →
        proj₁ (foldR resolve?Alg Γ r) ≡ just (proj₁ (foldR resolveAlg Γ r))

safeV Γ (ws-col lt)     = cong single? (resolveVar?-just Γ _ _ lt)
safeV Γ ws-lit          = refl
safeV Γ (ws-add {x} {y} wx wy)
  rewrite balV resolve?Alg Γ x | balV resolveAlg Γ x
        | safeV Γ wx | safeV Γ wy = refl
safeV Γ (ws-exists wr)
  rewrite safeR Γ wr = refl
safeR Γ ws-table        = refl
safeR Γ (ws-filtr {r} {p} wr wp)
  rewrite balR resolve?Alg Γ r | balR resolveAlg Γ r
        | safeR Γ wr
        | safeV (binds r ++ Γ)
                (subst (λ sh → WSV sh p) (sym (map-++-commute length (binds r) Γ)) wp)
        = refl
