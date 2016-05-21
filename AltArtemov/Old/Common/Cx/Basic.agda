module AltArtemov.Common.Cx.Basic where

open import AltArtemov.Common.Ty.Basic public


data Cx : Set where
  ∅   : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
