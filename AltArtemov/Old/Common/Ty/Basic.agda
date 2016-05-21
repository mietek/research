module AltArtemov.Common.Ty.Basic where

open import AltArtemov.Common.Tm public


data Ty : ℕ → Set where
  ⊥  : ∀ {n} → Ty n
  _⊃_ : ∀ {n} → Ty n → Ty n → Ty n
  _∧_ : ∀ {n} → Ty n → Ty n → Ty n
  _∶_ : ∀ {g n} → Tm g n → Ty n → Ty (suc n)

infixr 5 _⊃_
infixr 15 _∶_
