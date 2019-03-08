---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-AO

module 2-4-Properties-BigStep-AO where

open import 1-3-Semantics-BigStep
open AO public


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO goes to NF

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var              = nf var
nf-⇓ (lam r)          = lam (nf-⇓ r)
nf-⇓ (applam r₁ r₂ r) = nf-⇓ r
nf-⇓ (app r₁ p₁′ r₂)  = nf (app p₁″ (nf-⇓ r₂))
  where
    p₁″ = nanf←nf (nf-⇓ r₁) p₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nanf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
