-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

module Selinger92 where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_) renaming (lookup to get ; _[_]≔_ to put)


----------------------------------------------------------------------------------------------------

-- signatures
record Sig : Set where
  field
    #f      : ℕ -- number of functions
    arities : Vec ℕ #f -- arity of each function

  -- function index
  Fun : Set
  Fun = Fin (suc (suc #f))

  -- arity of f-th function
  arity : ∀ (f : Fun) → ℕ
  arity zero          = zero -- arity of 0
  arity (suc zero)    = suc zero -- arity of S
  arity (suc (suc n)) = get arities n

open Sig {{...}} public

module _ {{S : Sig}} where
  infix 17 `∀_ `∃_
  infixr 18 _`⊃_ _`⫗_
  infixl 19 _`∧_ _`∨_

  -- terms, indexed by number of numerical variables
  mutual
    data Tm (#v : ℕ) : Set where
      `var : ∀ (x : Fin #v) → Tm #v -- x-th numerical variable
      `fun : ∀ (f : Fun) (ts : Tms #v (arity f)) → Tm #v -- f-th function

    Tms : ∀ (#v #t : ℕ) → Set
    Tms #v #t = Vec (Tm #v) #t

  -- 0
  `zero : ∀ {#v} → Tm #v
  `zero = `fun zero []

  -- S
  `suc : ∀ {#v} (t : Tm #v) → Tm #v
  `suc t = `fun (suc zero) (t ∷ [])

  -- formulas, indexed by number of numerical variables
  data Fm (#v : ℕ) : Set where
    _`⊃_ : ∀ (A B : Fm #v) → Fm #v
    _`∧_ : ∀ (A B : Fm #v) → Fm #v
    _`∨_ : ∀ (A B : Fm #v) → Fm #v
    `∀_  : ∀ (B : Fm (suc #v)) → Fm #v
    `∃_  : ∀ (B : Fm (suc #v)) → Fm #v
    `⊥  : Fm #v
    _`=_ : ∀ (t u : Tm #v) → Fm #v

  Fms : ∀ (#v : ℕ) → Set
  Fms #v = List (Fm #v)

  `¬ : ∀ {#v} (A : Fm #v) → Fm #v
  `¬ A = A `⊃ `⊥

  _`⫗_ : ∀ {#v} (A B : Fm #v) → Fm #v
  A `⫗ B = (A `⊃ B) `∧ (B `⊃ A)

  _`≠_ : ∀ {#v} (t u : Tm #v) → Fm #v
  t `≠ u = `¬ (t `= u)


----------------------------------------------------------------------------------------------------

-- TODO: the usual
module _ {{S : Sig}} where
  postulate
    _∋_   : ∀ {#v} (Γ : Fms #v) (A : Fm #v) → Set
    wkfm  : ∀ {#v} (A : Fm #v) → Fm (suc #v)
    wkfms : ∀ {#v} (Γ : Fms #v) → Fms (suc #v)
    cutfm : ∀ {#v} (A : Fm (suc #v)) (s : Tm #v) → Fm #v


----------------------------------------------------------------------------------------------------

-- Heyting arithmetic
module HA {{S : Sig}} where
  -- derivations, indexed by assumptions
  infix 3 _⊢_
  data _⊢_ {#v} (Γ : Fms #v) : Fm #v → Set where
    `var   : ∀ {A} (a : Γ ∋ A) → Γ ⊢ A -- a-th assumption
    `lam   : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
    `app   : ∀ {A B} (d : Γ ⊢ A `⊃ B) (e : Γ ⊢ A) → Γ ⊢ B
    `pair  : ∀ {A B} (d : Γ ⊢ A) (e : Γ ⊢ B) → Γ ⊢ A `∧ B
    `fst   : ∀ {A B} (d : Γ ⊢ A `∧ B) → Γ ⊢ A
    `snd   : ∀ {A B} (d : Γ ⊢ A `∧ B) → Γ ⊢ B
    `left  : ∀ {A B} (d : Γ ⊢ A) → Γ ⊢ A `∨ B
    `right : ∀ {A B} (d : Γ ⊢ B) → Γ ⊢ A `∨ B
    `case  : ∀ {A B C} (c : Γ ⊢ A `∨ B) (d : A ∷ Γ ⊢ C) (e : B ∷ Γ ⊢ C) → Γ ⊢ C

    --  B[x]
    -- ------
    -- ∀xB[x]
    `∀intro : ∀ {B} (d : wkfms Γ ⊢ B) → Γ ⊢ `∀ B

    -- ∀xB[x]
    -- ------
    --  B[t]
    `∀elim : ∀ {B} (t : Tm #v) (d : Γ ⊢ `∀ B) → Γ ⊢ cutfm B t

    --  B[t]
    -- ------
    -- ∃xB[x]
    `∃intro : ∀ {B} (t : Tm #v) (d : Γ ⊢ cutfm B t) → Γ ⊢ `∃ B

    --          B[x]
    --           ⋮
    --   ∃xB[x]  C
    -- -------------
    --       C
    `∃elim : ∀ {B C} (d : Γ ⊢ `∃ B) (e : B ∷ wkfms Γ ⊢ wkfm C) → Γ ⊢ C

    `abort : ∀ {C} (d : Γ ⊢ `⊥) → Γ ⊢ C

    `refl  : ∀ {t} → Γ ⊢ t `= t
    `sym   : ∀ {t u} → Γ ⊢ t `= u → Γ ⊢ u `= t
    `trans : ∀ {s t u} → Γ ⊢ s `= t → Γ ⊢ t `= u → Γ ⊢ s `= u
    `cong  : ∀ f {ts u} i → Γ ⊢ get ts i `= u →
               Γ ⊢ `fun f ts `= `fun f (put ts i u)
    `suc₁  : ∀ {t} → Γ ⊢ `suc t `≠ `zero
    `suc₂  : ∀ {t u} → Γ ⊢ `suc t `= `suc u → Γ ⊢ t `= u
    `ind   : ∀ {B} → wkfms Γ ⊢ cutfm B `zero →
               Γ ⊢ `∀ cutfm B (`var zero) `⊃ cutfm B (`suc (`var zero)) →
               Γ ⊢ `∀ cutfm B (`var zero)

    -- TODO: axiom schemas for primitive recursive functions

  `congsuc : ∀ {#v} {Γ : Fms #v} {t u} → Γ ⊢ t `= u → Γ ⊢ `suc t `= `suc u
  `congsuc d = `cong (suc zero) zero d


----------------------------------------------------------------------------------------------------

-- TODO: Peano arithmetic
-- TODO: double-negation translation
-- TODO: A-translation


----------------------------------------------------------------------------------------------------
