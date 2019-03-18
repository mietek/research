---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-CBN

module 3-1-Properties-BigStep-CBN where

open import 2-1-Semantics-BigStep
open CBN public


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN goes to WHNF

whnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → WHNF e′
whnf-⟱ (applam r₁ r) = whnf-⟱ r
whnf-⟱ var           = whnf var
whnf-⟱ lam           = lam
whnf-⟱ (app r₁ p₁′)  = whnf (app p₁″)
  where
    p₁″ = naxnf←whnf (whnf-⟱ r₁) p₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN is reflexive

refl-⟱′ : ∀ {n} {e : Tm n} → NAXNF e → e ⟱ e
refl-⟱′ var      = var
refl-⟱′ (app p₁) = app (refl-⟱′ p₁) (na←naxnf p₁)

refl-⟱ : ∀ {n} {e : Tm n} → WHNF e → e ⟱ e
refl-⟱ lam      = lam
refl-⟱ (whnf p) = refl-⟱′ p


---------------------------------------------------------------------------------------------------------------
