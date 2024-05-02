---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-CBV

module A201903.3-3-Properties-BigStep-CBV where

open import A201903.2-1-Semantics-BigStep
open CBV public


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV goes to WNF

wnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → WNF e′
wnf-⟱ (applam r₁ r₂ r) = wnf-⟱ r
wnf-⟱ var              = wnf var
wnf-⟱ lam              = lam
wnf-⟱ (app r₁ p₁′ r₂)  = wnf (app p₁″ (wnf-⟱ r₂))
  where
    p₁″ = nawnf←wnf (wnf-⟱ r₁) p₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV is reflexive

mutual
  refl-⟱ : ∀ {n} {e : Tm n} → WNF e → e ⟱ e
  refl-⟱ lam     = lam
  refl-⟱ (wnf p) = refl-⟱′ p

  refl-⟱′ : ∀ {n} {e : Tm n} → NAWNF e → e ⟱ e
  refl-⟱′ (var)       = var
  refl-⟱′ (app p₁ p₂) = app (refl-⟱′ p₁) (na←nawnf p₁) (refl-⟱ p₂)


---------------------------------------------------------------------------------------------------------------
