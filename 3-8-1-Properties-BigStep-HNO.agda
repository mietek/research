---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-HNO

module 3-8-1-Properties-BigStep-HNO where

open import 2-1-Semantics-BigStep
open HNO public
import 3-6-Properties-BigStep-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO goes to NF

na←naxnf-hs-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e HS.⟱ e′ → NA e′
na←naxnf-hs-⟱ var      HS.var           = var
na←naxnf-hs-⟱ (app p₁) (HS.applam r₁ r) = case (na←naxnf-hs-⟱ p₁ r₁) of λ ()
na←naxnf-hs-⟱ (app p₁) (HS.app r₁ p₁′)  = app

na←naxnf-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⟱ e′ → NA e′
na←naxnf-⟱ var      var                 = var
na←naxnf-⟱ (app p₁) (applam r₁ r)       = case (na←naxnf-hs-⟱ p₁ r₁) of λ ()
na←naxnf-⟱ (app p₁) (app r₁ p₁′ r₁′ r₂) = app

na←hnf-⟱ : ∀ {n} {e : Tm n} {e′} → HNF e → NA e → e ⟱ e′ → NA e′
na←hnf-⟱ (lam p) () r
na←hnf-⟱ (hnf p) p′ r = na←naxnf-⟱ p r

nf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → NF e′
nf-⟱ (applam r₁ r)       = nf-⟱ r
nf-⟱ var                 = nf var
nf-⟱ (lam r)             = lam (nf-⟱ r)
nf-⟱ (app r₁ p₁′ r₁′ r₂) = nf (app p₁ (nf-⟱ r₂))
  where
    p₁ = nanf←nf (nf-⟱ r₁′) (na←hnf-⟱ (HS.hnf-⟱ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO is reflexive

mutual
  refl-⟱ : ∀ {n} {e : Tm n} → NF e → e ⟱ e
  refl-⟱ (lam p) = lam (refl-⟱ p)
  refl-⟱ (nf p)  = refl-⟱′ p

  refl-⟱′ : ∀ {n} {e : Tm n} → NANF e → e ⟱ e
  refl-⟱′ (var)       = var
  refl-⟱′ (app p₁ p₂) = app (HS.refl-⟱′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⟱′ p₁) (refl-⟱ p₂)


---------------------------------------------------------------------------------------------------------------
