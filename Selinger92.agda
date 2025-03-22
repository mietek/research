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

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

-- derivations, indexed by assumptions
infix 3 _⊢[_]_
data _⊢[_]_ {k} (Γ : Fms k) : Theory → Fm k → Set where
  `var    : ∀ {Θ A} (a : Γ ∋ A) → Γ ⊢[ Θ ] A -- a-th assumption
  `lam    : ∀ {Θ A B} (d : A ∷ Γ ⊢[ Θ ] B) → Γ ⊢[ Θ ] A `⊃ B
  _`$_    : ∀ {Θ A B} (d : Γ ⊢[ Θ ] A `⊃ B) (e : Γ ⊢[ Θ ] A) → Γ ⊢[ Θ ] B
  `pair   : ∀ {Θ A B} (d : Γ ⊢[ Θ ] A) (e : Γ ⊢[ Θ ] B) → Γ ⊢[ Θ ] A `∧ B
  `fst    : ∀ {Θ A B} (d : Γ ⊢[ Θ ] A `∧ B) → Γ ⊢[ Θ ] A
  `snd    : ∀ {Θ A B} (d : Γ ⊢[ Θ ] A `∧ B) → Γ ⊢[ Θ ] B
  `left   : ∀ {Θ A B} (d : Γ ⊢[ Θ ] A) → Γ ⊢[ Θ ] A `∨ B
  `right  : ∀ {Θ A B} (d : Γ ⊢[ Θ ] B) → Γ ⊢[ Θ ] A `∨ B
  `case   : ∀ {Θ A B C} (c : Γ ⊢[ Θ ] A `∨ B) (d : A ∷ Γ ⊢[ Θ ] C) (e : B ∷ Γ ⊢[ Θ ] C) →
              Γ ⊢[ Θ ] C

  --  B[x]
  -- ------
  -- ∀xB[x]
  `∀intro : ∀ {Θ B} (d : wkfms Γ ⊢[ Θ ] B) → Γ ⊢[ Θ ] `∀ B

  -- ∀xB[x]
  -- ------
  --  B[t]
  `∀elim  : ∀ {Θ B} (t : Tm k) (d : Γ ⊢[ Θ ] `∀ B) → Γ ⊢[ Θ ] cutfm B t

  --  B[t]
  -- ------
  -- ∃xB[x]
  `∃intro : ∀ {Θ B} (t : Tm k) (d : Γ ⊢[ Θ ] cutfm B t) → Γ ⊢[ Θ ] `∃ B

  --          B[x]
  --           ⋮
  --   ∃xB[x]  C
  -- -------------
  --       C
  `∃elim  : ∀ {Θ B C} (d : Γ ⊢[ Θ ] `∃ B) (e : B ∷ wkfms Γ ⊢[ Θ ] wkfm C) → Γ ⊢[ Θ ] C

  `abort  : ∀ {C} (d : Γ ⊢[ HA ] `⊥) → Γ ⊢[ HA ] C
  `magic  : ∀ {A} (d : `¬ A ∷ Γ ⊢[ PA ] `⊥) → Γ ⊢[ PA ] A

  `refl   : ∀ {Θ t} → Γ ⊢[ Θ ] t `= t
  `sym    : ∀ {Θ t u} → Γ ⊢[ Θ ] t `= u → Γ ⊢[ Θ ] u `= t
  `trans  : ∀ {Θ s t u} → Γ ⊢[ Θ ] s `= t → Γ ⊢[ Θ ] t `= u → Γ ⊢[ Θ ] s `= u
  `cong   : ∀ {Θ n ts u} (φ : Fun n) (i : Fin n) → Γ ⊢[ Θ ] get ts i `= u →
              Γ ⊢[ Θ ] `fun φ ts `= `fun φ (put ts i u)
  `suc₁   : ∀ {Θ t} → Γ ⊢[ Θ ] `suc t `≠ `zero
  `suc₂   : ∀ {Θ t u} → Γ ⊢[ Θ ] `suc t `= `suc u → Γ ⊢[ Θ ] t `= u
  `ind    : ∀ {Θ B} → wkfms Γ ⊢[ Θ ] cutfm B `zero →
              Γ ⊢[ Θ ] `∀ cutfm B (`var zero) `⊃ cutfm B (`suc (`var zero)) →
              Γ ⊢[ Θ ] `∀ cutfm B (`var zero)
  `proj   : ∀ {Θ n ts} (i : Fin n) → Γ ⊢[ Θ ] `fun (proj i) ts `= get ts i
  `comp   : ∀ {Θ n m ts} (φs : Vec (Fun n) m) (ψ : Fun m) →
              Γ ⊢[ Θ ] `fun (comp φs ψ) ts `= `fun ψ (map (λ φ → `fun φ ts) φs)
  `rec    : ∀ {Θ n s ts} (φ : Fun n) (ψ : Fun (suc (suc n))) →
              Γ ⊢[ Θ ] `fun (rec φ ψ) (`zero ∷ ts) `= `fun φ ts `∧
                `fun (rec φ ψ) (`suc s ∷ ts) `= `fun ψ (`fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts)

`congsuc : ∀ {Θ k} {Γ : Fms k} {t u} → Γ ⊢[ Θ ] t `= u → Γ ⊢[ Θ ] `suc t `= `suc u
`congsuc d = `cong suc zero d

infix 3 _⊢HA_
_⊢HA_ : ∀ {k} → Fms k → Fm k → Set
Γ ⊢HA A = Γ ⊢[ HA ] A

infix 3 _⊢PA_
_⊢PA_ : ∀ {k} → Fms k → Fm k → Set
Γ ⊢PA A = Γ ⊢[ PA ] A


----------------------------------------------------------------------------------------------------

-- TODO: double-negation translation
-- TODO: A-translation


----------------------------------------------------------------------------------------------------
