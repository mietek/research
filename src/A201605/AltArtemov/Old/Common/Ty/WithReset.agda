module A201605.AltArtemov.Old.Common.Ty.WithReset where

open import A201605.AltArtemov.Try2.Tm public


data Ty : ℕ → Set where
  ⊥  : Ty 0
  _⊃_ : ∀ {n n′} → Ty n → Ty n′ → Ty 0
  _∧_ : ∀ {n n′} → Ty n → Ty n′ → Ty 0
  _∶_ : ∀ {g n} → Tm g n → Ty n → Ty (suc n)

infixr 5 _⊃_
infixr 15 _∶_

tm : ∀ {n} → Ty (suc n) → ∃ (λ g → Tm g n)
tm (t ∶ A) = (_ , t)

--
--A : Ty n
--B : Ty n′
--
--A ⊃ A     : Ty 0
--A ⊃ B ⊃ A : Ty 0
--
--f ∶ (A ⊃ B)                         : Ty 1
--x ∶ A                               : Ty (n + 1)
--APP f x ∶ B                         : Ty (n′ + 1)
--x ∶ A ⊃ (APP f x) ∶ B               : Ty 0
--f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (APP f x) ∶ B : Ty 0
