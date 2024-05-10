module A201605.AltArtemov.Try3.Cx where

open import A201605.AltArtemov.Try3.Ty public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {k} → Cx → Ty k → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
