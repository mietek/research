module Context (Type : Set) where

open import Prelude
open import Category

------------------------------------------------------------------------------

-- Intrinsically well-typed contexts.
data Context : Set where
  ·   : Context
  _,_ : Context → Type → Context

-- Intrinsically well-typed de Bruijn indices.
infix 3 _∋_
data _∋_ : Context → Type → Set where
  top : ∀ {Γ A} → Γ , A ∋ A
  pop : ∀ {Γ A C} → Γ ∋ A → Γ , C ∋ A

------------------------------------------------------------------------------
