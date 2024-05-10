module A201605.AltArtemov.Try2.Ty where

open import A201605.AltArtemov.Try2.Tm public


data Ty : ℕ → Set where
  ⊥  : ∀ {n} → Ty n
  _⊃_ : ∀ {n} → Ty n → Ty n → Ty n
  _∧_ : ∀ {n} → Ty n → Ty n → Ty n
  _∶_ : ∀ {g n} → Tm g n → Ty n → Ty (suc n)

infixr 5 _⊃_
infixr 15 _∶_
