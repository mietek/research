module A201605.AltArtemov.Library.Fin where

open import A201605.AltArtemov.Library.O public


ren-fin : ∀ {g g′} → g′ ≥ g → Fin g → Fin g′
ren-fin base     i       = i
ren-fin (weak h) i       = suc (ren-fin h i)
ren-fin (lift h) zero    = zero
ren-fin (lift h) (suc i) = suc (ren-fin h i)

wk-fin : ∀ {g} → Fin g → Fin (suc g)
wk-fin = ren-fin ≥wk

wk*-fin : ∀ {g} → Fin 0 → Fin g
wk*-fin ()

ren-fin-id : ∀ {g} (i : Fin g) → ren-fin ≥id i ≡ i
ren-fin-id zero    = refl
ren-fin-id (suc i) = cong suc (ren-fin-id i)

ren-fin-○ : ∀ {g g′ g″} (h′ : g″ ≥ g′) (h : g′ ≥ g) (i : Fin g) →
              ren-fin h′ (ren-fin h i) ≡ ren-fin (h′ ○ h) i
ren-fin-○ base      h        i       = refl
ren-fin-○ (weak h′) h        i       = cong suc (ren-fin-○ h′ h i)
ren-fin-○ (lift h′) (weak h) i       = cong suc (ren-fin-○ h′ h i)
ren-fin-○ (lift h′) (lift h) zero    = refl
ren-fin-○ (lift h′) (lift h) (suc i) = cong suc (ren-fin-○ h′ h i)

i₀ : ∀ {g} → Fin (suc g)
i₀ = zero

i₁ : ∀ {g} → Fin (suc (suc g))
i₁ = suc i₀

i₂ : ∀ {g} → Fin (suc (suc (suc g)))
i₂ = suc i₁
