module A201605.AltArtemov.Try1.Cx where

open import A201605.AltArtemov.Try1.Ty public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
