---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-H₂

module A201903.3-7-1-Properties-BigStep-H₂ where

open import A201903.2-1-Semantics-BigStep
open H₂ public
import A201903.3-1-Properties-BigStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-H₂ goes from WHNF to HNF

na←naxnf-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⟱ e′ → NA e′
na←naxnf-⟱ var      var          = var
na←naxnf-⟱ (app p₁) (app p₁′ r₁) = app

na←whnf-⟱ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⟱ e′ → NA e′
na←whnf-⟱ lam      () r
na←whnf-⟱ (whnf p) p′ r = na←naxnf-⟱ p r

hnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → HNF e′
hnf-⟱ var         = hnf var
hnf-⟱ (lam r r′)  = lam (hnf-⟱ r′)
hnf-⟱ (app p₁ r₁) = hnf (app p₁′)
  where
    p₁′ = naxnf←hnf (hnf-⟱ r₁) (na←naxnf-⟱ p₁ r₁)

rev-whnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → WHNF e
rev-whnf-⟱ var         = whnf var
rev-whnf-⟱ (lam r r′)  = lam
rev-whnf-⟱ (app p₁ r₁) = whnf (app p₁)


---------------------------------------------------------------------------------------------------------------
--
-- BS-H₂ is reflexive

mutual
  refl-⟱ : ∀ {n} {e : Tm n} → HNF e → e ⟱ e
  refl-⟱ (lam p) = lam (CBN.refl-⟱ (whnf←hnf p)) (refl-⟱ p)
  refl-⟱ (hnf p) = refl-⟱′ p

  refl-⟱′ : ∀ {n} {e : Tm n} → NAXNF e → e ⟱ e
  refl-⟱′ var      = var
  refl-⟱′ (app p₁) = app p₁ (refl-⟱′ p₁)


---------------------------------------------------------------------------------------------------------------
