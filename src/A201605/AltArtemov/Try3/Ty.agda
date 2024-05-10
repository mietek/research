module A201605.AltArtemov.Try3.Ty where

open import A201605.AltArtemov.Try3.Tm public


data Ty : ℕ → Set where
  ⊥  : Ty 0
  _⊃_ : ∀ {k k′} → Ty k → Ty k′ → Ty 0
  _∧_ : ∀ {k k′} → Ty k → Ty k′ → Ty 0
  _∶_ : ∀ {g k} → Tm g k → Ty k → Ty (suc k)

infixr 5 _⊃_
infixr 15 _∶_

lev : ∀ {k} → Ty k → ℕ
lev {k} A = k

tm : ∀ {k} → Ty (suc k) → ∃ (λ g → Tm g k)
tm (t ∶ A) = (_ , t)
