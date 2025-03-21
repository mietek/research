-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

module Selinger92 where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map) renaming (lookup to get ; _[_]≔_ to put)


----------------------------------------------------------------------------------------------------

-- primitive recursive functions, indexed by arity

data PRFun : ℕ → Set where
  zero : PRFun zero
  suc  : PRFun (suc zero)
  proj : ∀ {n} (i : Fin n) → PRFun n
  comp : ∀ {n m} (φs : Vec (PRFun n) m) (ψ : PRFun m) → PRFun n
  rec  : ∀ {n} (φ : PRFun n) (ψ : PRFun (suc (suc n))) → PRFun (suc n)

mutual
  ⟦_⟧ : ∀ {n} → PRFun n → Vec ℕ n → ℕ
  ⟦ zero ⟧      []       = zero
  ⟦ suc ⟧       (y ∷ []) = suc y
  ⟦ proj i ⟧    xs       = get xs i
  ⟦ comp φs ψ ⟧ xs       = ⟦ ψ ⟧ (⟦ φs ⟧* xs)
  ⟦ rec φ ψ ⟧   (y ∷ xs) = ⟦rec⟧ φ ψ y xs

  ⟦_⟧* : ∀ {n m} → Vec (PRFun n) m → Vec ℕ n → Vec ℕ m
  ⟦ [] ⟧*     xs = []
  ⟦ φ ∷ φs ⟧* xs = ⟦ φ ⟧ xs ∷ ⟦ φs ⟧* xs

  ⟦rec⟧ : ∀ {n} → PRFun n → PRFun (suc (suc n)) → ℕ → Vec ℕ n → ℕ
  ⟦rec⟧ φ ψ zero    xs = ⟦ φ ⟧ xs
  ⟦rec⟧ φ ψ (suc y) xs = ⟦ ψ ⟧ (⟦rec⟧ φ ψ y xs ∷ y ∷ xs)


----------------------------------------------------------------------------------------------------

infix 17 `∀_ `∃_
infixr 18 _`⊃_ _`⫗_
infixl 19 _`∧_ _`∨_

-- terms, indexed by number of numerical variables
mutual
  data Tm (#v : ℕ) : Set where
    `var : ∀ (x : Fin #v) → Tm #v -- x-th numerical variable
    `fun : ∀ {n} (φ : PRFun n) (ts : Tms #v n) → Tm #v

  Tms : ∀ (#v #t : ℕ) → Set
  Tms #v #t = Vec (Tm #v) #t

  -- 0
  `zero : ∀ {#v} → Tm #v
  `zero = `fun zero []

  -- S
  `suc : ∀ {#v} (t : Tm #v) → Tm #v
  `suc t = `fun suc (t ∷ [])

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
postulate
  _∋_   : ∀ {#v} (Γ : Fms #v) (A : Fm #v) → Set
  wkfm  : ∀ {#v} (A : Fm #v) → Fm (suc #v)
  wkfms : ∀ {#v} (Γ : Fms #v) → Fms (suc #v)
  cutfm : ∀ {#v} (A : Fm (suc #v)) (s : Tm #v) → Fm #v


----------------------------------------------------------------------------------------------------

-- Heyting arithmetic
module HA where
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
    `cong  : ∀ {n ts u} (φ : PRFun n) (i : Fin n) → Γ ⊢ get ts i `= u →
               Γ ⊢ `fun φ ts `= `fun φ (put ts i u)
    `suc₁  : ∀ {t} → Γ ⊢ `suc t `≠ `zero
    `suc₂  : ∀ {t u} → Γ ⊢ `suc t `= `suc u → Γ ⊢ t `= u
    `ind   : ∀ {B} → wkfms Γ ⊢ cutfm B `zero →
               Γ ⊢ `∀ cutfm B (`var zero) `⊃ cutfm B (`suc (`var zero)) →
               Γ ⊢ `∀ cutfm B (`var zero)
    `proj  : ∀ {n ts} (i : Fin n) → Γ ⊢ `fun (proj i) ts `= get ts i
    `comp  : ∀ {n m ts} (φs : Vec (PRFun n) m) (ψ : PRFun m) →
               Γ ⊢ `fun (comp φs ψ) ts `= `fun ψ (map (λ φ → `fun φ ts) φs)
    `rec   : ∀ {n s ts} (φ : PRFun n) (ψ : PRFun (suc (suc n))) →
               Γ ⊢ (`fun (rec φ ψ) (`zero ∷ ts) `= `fun φ ts) `∧
                    (`fun (rec φ ψ) (`suc s ∷ ts) `= `fun ψ (`fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts))

  `congsuc : ∀ {#v} {Γ : Fms #v} {t u} → Γ ⊢ t `= u → Γ ⊢ `suc t `= `suc u
  `congsuc d = `cong suc zero d


----------------------------------------------------------------------------------------------------

-- TODO: Peano arithmetic
-- TODO: double-negation translation
-- TODO: A-translation


----------------------------------------------------------------------------------------------------
