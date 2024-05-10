module A201605.AltArtemov.Old.Common.Cx.WithReset where

open import A201605.AltArtemov.Old.Common.Ty.WithReset public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
