-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

module Selinger92 where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; foldr′)
  renaming (lookup to get ; _[_]≔_ to put)

recℕ : ∀ {a} {A : Set a} → A → (ℕ → A → A) → ℕ → A
recℕ a f zero    = a
recℕ a f (suc n) = f n (recℕ a f n)


----------------------------------------------------------------------------------------------------

-- primitive recursive functions, indexed by arity
data Fun : ℕ → Set where
  zero : Fun zero
  suc  : Fun (suc zero)
  proj : ∀ {n} (i : Fin n) → Fun n
  comp : ∀ {n m} (φs : Vec (Fun n) m) (ψ : Fun m) → Fun n
  rec  : ∀ {n} (φ : Fun n) (ψ : Fun (suc (suc n))) → Fun (suc n)

-- standard model
mutual
  ⟦_⟧ : ∀ {n} → Fun n → Vec ℕ n → ℕ
  ⟦ zero ⟧      []       = zero
  ⟦ suc ⟧       (x ∷ []) = suc x
  ⟦ proj i ⟧    xs       = get xs i
  ⟦ comp φs ψ ⟧ xs       = ⟦ ψ ⟧ (⟦ φs ⟧* xs)
  ⟦ rec φ ψ ⟧   (y ∷ xs) = recℕ (⟦ φ ⟧ xs) (λ y r → ⟦ ψ ⟧ (r ∷ y ∷ xs)) y

  ⟦_⟧* : ∀ {n m} → Vec (Fun n) m → Vec ℕ n → Vec ℕ m
  ⟦ [] ⟧*     xs = []
  ⟦ φ ∷ φs ⟧* xs = ⟦ φ ⟧ xs ∷ ⟦ φs ⟧* xs


----------------------------------------------------------------------------------------------------

infix 16 `¬_
infix 17 `∀_ `∃_
infixr 18 _`⊃_ _`⫗_
infixl 19 _`∧_ _`∨_

-- terms, indexed by number of numerical variables
mutual
  data Tm (k : ℕ) : Set where
    `var : ∀ (x : Fin k) → Tm k -- x-th numerical variable
    `fun : ∀ {n} (φ : Fun n) (ts : Tms k n) → Tm k

  Tms : ℕ → ℕ → Set
  Tms k = Vec (Tm k)

`zero : ∀ {k} → Tm k
`zero = `fun zero []

`suc : ∀ {k} → Tm k → Tm k
`suc t = `fun suc (t ∷ [])

-- formulas, indexed by number of numerical variables
data Fm (k : ℕ) : Set where
  _`⊃_ : ∀ (A B : Fm k) → Fm k
  _`∧_ : ∀ (A B : Fm k) → Fm k
  _`∨_ : ∀ (A B : Fm k) → Fm k
  `∀_  : ∀ (B : Fm (suc k)) → Fm k
  `∃_  : ∀ (B : Fm (suc k)) → Fm k
  `⊥  : Fm k
  _`=_ : ∀ (t u : Tm k) → Fm k

Fms : ℕ → Set
Fms k = List (Fm k)

`¬_ : ∀ {k} → Fm k → Fm k
`¬ A = A `⊃ `⊥

_`⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A `⫗ B = (A `⊃ B) `∧ (B `⊃ A)

_`≠_ : ∀ {k} → Tm k → Tm k → Fm k
t `≠ u = `¬ t `= u


----------------------------------------------------------------------------------------------------

-- TODO: the usual
postulate
  _∋_   : ∀ {k} (Γ : Fms k) (A : Fm k) → Set
  wkfm  : ∀ {k} (A : Fm k) → Fm (suc k)
  wkfms : ∀ {k} (Γ : Fms k) → Fms (suc k)
  cutfm : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k


----------------------------------------------------------------------------------------------------

-- Heyting arithmetic
module HA where
  -- derivations, indexed by assumptions
  infix 3 _⊢_
  data _⊢_ {k} (Γ : Fms k) : Fm k → Set where
    `var   : ∀ {A} (a : Γ ∋ A) → Γ ⊢ A -- a-th assumption
    `lam   : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
    _`$_   : ∀ {A B} (d : Γ ⊢ A `⊃ B) (e : Γ ⊢ A) → Γ ⊢ B
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
    `∀elim : ∀ {B} (t : Tm k) (d : Γ ⊢ `∀ B) → Γ ⊢ cutfm B t

    --  B[t]
    -- ------
    -- ∃xB[x]
    `∃intro : ∀ {B} (t : Tm k) (d : Γ ⊢ cutfm B t) → Γ ⊢ `∃ B

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
    `cong  : ∀ {n ts u} (φ : Fun n) (i : Fin n) → Γ ⊢ get ts i `= u →
               Γ ⊢ `fun φ ts `= `fun φ (put ts i u)
    `suc₁  : ∀ {t} → Γ ⊢ `suc t `≠ `zero
    `suc₂  : ∀ {t u} → Γ ⊢ `suc t `= `suc u → Γ ⊢ t `= u
    `ind   : ∀ {B} → wkfms Γ ⊢ cutfm B `zero →
               Γ ⊢ `∀ cutfm B (`var zero) `⊃ cutfm B (`suc (`var zero)) →
               Γ ⊢ `∀ cutfm B (`var zero)
    `proj  : ∀ {n ts} (i : Fin n) → Γ ⊢ `fun (proj i) ts `= get ts i
    `comp  : ∀ {n m ts} (φs : Vec (Fun n) m) (ψ : Fun m) →
               Γ ⊢ `fun (comp φs ψ) ts `= `fun ψ (map (λ φ → `fun φ ts) φs)
    `rec   : ∀ {n s ts} (φ : Fun n) (ψ : Fun (suc (suc n))) →
               Γ ⊢ `fun (rec φ ψ) (`zero ∷ ts) `= `fun φ ts
                 `∧ `fun (rec φ ψ) (`suc s ∷ ts) `= `fun ψ (`fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts)

  `congsuc : ∀ {k} {Γ : Fms k} {t u} → Γ ⊢ t `= u → Γ ⊢ `suc t `= `suc u
  `congsuc d = `cong suc zero d


----------------------------------------------------------------------------------------------------

-- TODO: Peano arithmetic
-- TODO: double-negation translation
-- TODO: A-translation


----------------------------------------------------------------------------------------------------
