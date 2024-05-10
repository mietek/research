module A201605.AltArtemov.Old.Common.Cx.WithGMutual where

open import A201605.AltArtemov.Old.Common.Ty.WithG public


mutual
  data Cx : Set where
    ∅   : Cx
    _,_ : ∀ {n} (Γ : Cx) → Ty ᵍ⌊ Γ ⌋ n → Cx

  ᵍ⌊_⌋ : Cx → ℕ
  ᵍ⌊ ∅ ⌋     = zero
  ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
