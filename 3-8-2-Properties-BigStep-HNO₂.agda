---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-HNO₂

module 3-8-2-Properties-BigStep-HNO₂ where

open import 2-1-Semantics-BigStep
open HNO₂ public
import 3-6-Properties-BigStep-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO₂ goes from HNF to NF

na←naxnf-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⟱ e′ → NA e′
na←naxnf-⟱ var      var                 = var
na←naxnf-⟱ (app p₁) (app p₁′ r₁ r₂ r₂′) = app

na←hnf-⟱ : ∀ {n} {e : Tm n} {e′} → HNF e → NA e → e ⟱ e′ → NA e′
na←hnf-⟱ (lam p) () r
na←hnf-⟱ (hnf p) p′ r = na←naxnf-⟱ p r

nf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → NF e′
nf-⟱ var                = nf var
nf-⟱ (lam r r′)         = lam (nf-⟱ r′)
nf-⟱ (app p₁ r₁ r₂ r₂′) = nf (app p₁′ (nf-⟱ r₂′))
  where
    p₁′ = nanf←nf (nf-⟱ r₁) (na←naxnf-⟱ p₁ r₁)

rev-hnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → HNF e
rev-hnf-⟱ var                = hnf var
rev-hnf-⟱ (lam p r)          = lam p
rev-hnf-⟱ (app p₁ r₁ r₂ r₂′) = hnf (app p₁)


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO₂ is reflexive

mutual
  refl-⟱ : ∀ {n} {e : Tm n} → NF e → e ⟱ e
  refl-⟱ (lam p) = lam (hnf←nf p) (refl-⟱ p)
  refl-⟱ (nf p)  = refl-⟱′ p

  refl-⟱′ : ∀ {n} {e : Tm n} → NANF e → e ⟱ e
  refl-⟱′ var         = var
  refl-⟱′ (app p₁ p₂) = app (naxnf←nanf p₁) (refl-⟱′ p₁) (HS.refl-⟱ (hnf←nf p₂)) (refl-⟱ p₂)


---------------------------------------------------------------------------------------------------------------
