---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-CBV

module Properties-BigStep-CBV where

open import Semantics-BigStep
open CBV public


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV goes to WNF

wnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WNF e′
wnf-⇓ var              = wnf var
wnf-⇓ lam              = lam
wnf-⇓ (applam r₁ r₂ r) = wnf-⇓ r
wnf-⇓ (app r₁ q₁′ r₂)  = wnf (app (nawnf←wnf (wnf-⇓ r₁) q₁′) (wnf-⇓ r₂))


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → WNF e → e ⇓ e
  refl-⇓ lam     = lam
  refl-⇓ (wnf p) = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NAWNF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nawnf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
