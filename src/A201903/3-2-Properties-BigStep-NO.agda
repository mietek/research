{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-NO

module A201903.3-2-Properties-BigStep-NO where

open import A201903.2-1-Semantics-BigStep
open NO public
import A201903.3-1-Properties-BigStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO goes to NF

na←naxnf-cbn-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e CBN.⟱ e′ → NA e′
na←naxnf-cbn-⟱ var      CBN.var           = var
na←naxnf-cbn-⟱ (app p₁) (CBN.applam r₁ r) = case p₁′ of λ ()
  where
    p₁′ = naxnf←whnf (CBN.whnf-⟱ r₁) (na←naxnf-cbn-⟱ p₁ r₁)
na←naxnf-cbn-⟱ (app p₁) (CBN.app r₁ p₁′)  = app

na←naxnf-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⟱ e′ → NA e′
na←naxnf-⟱ var      var                 = var
na←naxnf-⟱ (app p₁) (applam r₁ r)       = case (na←naxnf-cbn-⟱ p₁ r₁) of λ ()
na←naxnf-⟱ (app p₁) (app r₁ p₁′ r₁′ r₂) = app

na←whnf-⟱ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⟱ e′ → NA e′
na←whnf-⟱ lam      () r
na←whnf-⟱ (whnf p) p′ r = na←naxnf-⟱ p r

nf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → NF e′
nf-⟱ (applam r₁ r)       = nf-⟱ r
nf-⟱ var                 = nf var
nf-⟱ (lam r)             = lam (nf-⟱ r)
nf-⟱ (app r₁ p₁′ r₁′ r₂) = nf (app p₁″ (nf-⟱ r₂))
  where
    p₁″ = nanf←nf (nf-⟱ r₁′) (na←whnf-⟱ (CBN.whnf-⟱ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO is reflexive

mutual
  refl-⟱ : ∀ {n} {e : Tm n} → NF e → e ⟱ e
  refl-⟱ (lam p) = lam (refl-⟱ p)
  refl-⟱ (nf p)  = refl-⟱′ p

  refl-⟱′ : ∀ {n} {e : Tm n} → NANF e → e ⟱ e
  refl-⟱′ var         = var
  refl-⟱′ (app p₁ p₂) = app (CBN.refl-⟱′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⟱′ p₁) (refl-⟱ p₂)


---------------------------------------------------------------------------------------------------------------
