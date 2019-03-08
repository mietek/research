---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-HNO₂

module 3-8-2-Properties-BigStep-HNO₂ where

open import 1-4-Semantics-BigStep
open HNO₂ public
import 3-6-Properties-BigStep-HS as BS-HS


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO₂ goes from WHNF to NF

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                 = var
na←naxnf-⇓ (app p₁) (app p₁′ r₁ r₂ r₂′) = app

na←whnf-⇓ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⇓ e′ → NA e′
na←whnf-⇓ lam      () r
na←whnf-⇓ (whnf p) p′ r = na←naxnf-⇓ p r

rev-whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e
rev-whnf-⇓ var                = whnf var
rev-whnf-⇓ (lam r r′)         = lam
rev-whnf-⇓ (app p₁ r₁ r₂ r₂′) = whnf (app (naxnf←whnf (rev-whnf-⇓ r₁) p₁))

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r r′)         = lam (nf-⇓ r′)
nf-⇓ (app p₁ r₁ r₂ r₂′) = nf (app p₁′ (nf-⇓ r₂′))
  where
    p₁′ = nanf←nf (nf-⇓ r₁) (na←whnf-⇓ (rev-whnf-⇓ r₁) p₁ r₁)


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO₂ is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (BS-HS.refl-⇓ (hnf←nf p)) (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (na←nanf p₁) (refl-⇓′ p₁) (BS-HS.refl-⇓ (hnf←nf p₂)) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
