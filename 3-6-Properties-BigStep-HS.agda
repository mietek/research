---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-HS

module 3-6-Properties-BigStep-HS where

open import 1-4-Semantics-BigStep
open HS public


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS goes to HNF

hnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → HNF e′
hnf-⇓ var           = hnf var
hnf-⇓ (lam r)       = lam (hnf-⇓ r)
hnf-⇓ (applam r₁ r) = hnf-⇓ r
hnf-⇓ (app r₁ p₁′)  = hnf (app p₁″)
  where
    p₁″ = naxnf←hnf (hnf-⇓ r₁) p₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS is reflexive

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var      = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → HNF e → e ⇓ e
refl-⇓ (lam p) = lam (refl-⇓ p)
refl-⇓ (hnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------
