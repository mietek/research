module AltArtemov.Common.Cx.WithGUniform where

open import AltArtemov.Common.Ty.WithG public


data Cx (g : ℕ) : Set where
  ∅   : Cx g
  _,_ : ∀ {n} → Cx g → Ty g n → Cx g

ᵍ⌊_⌋ : ∀ {g} → Cx g → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋

ren-cx : ∀ {g g′} → g′ ≥ g → Cx g → Cx g′
ren-cx h ∅       = ∅
ren-cx h (Γ , A) = ren-cx h Γ , ren-ty h A

wk-cx : ∀ {g} → Cx g → Cx (suc g)
wk-cx = ren-cx ≥wk

wk*-cx : ∀ {g} → Cx 0 → Cx g
wk*-cx = ren-cx ≥to

ren-cx-id : ∀ {g} (Γ : Cx g) → ren-cx ≥id Γ ≡ Γ
ren-cx-id ∅       = refl
ren-cx-id (Γ , A) = cong₂ _,_ (ren-cx-id Γ) (ren-ty-id A)

ren-cx-○ : ∀ {g g′ g″} (h′ : g″ ≥ g′) (h : g′ ≥ g) (Γ : Cx g) →
             ren-cx h′ (ren-cx h Γ) ≡ ren-cx (h′ ○ h) Γ
ren-cx-○ h′ h ∅       = refl
ren-cx-○ h′ h (Γ , A) = cong₂ _,_ (ren-cx-○ h′ h Γ) (ren-ty-○ h′ h A)
