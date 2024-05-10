module AltArtemov.Old.Common.Cx.WithG where

open import AltArtemov.Old.Common.Ty.WithG public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {n} → Cx → Ty 0 n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
