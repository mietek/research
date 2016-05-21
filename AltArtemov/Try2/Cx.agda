module AltArtemov.Try2.Cx where

open import AltArtemov.Try2.Ty public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
