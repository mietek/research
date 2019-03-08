---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-H

module 3-7-1-Properties-BigStep-H where

open import 1-4-Semantics-BigStep
open H public
import 3-1-Properties-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-H goes to HNF

hnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → HNF e′
hnf-⇓ var           = hnf var
hnf-⇓ (lam r)       = lam (hnf-⇓ r)
hnf-⇓ (applam r₁ r) = hnf-⇓ r
hnf-⇓ (app r₁ p₁′)  = hnf (app (naxnf←whnf (BS-CBN.whnf-⇓ r₁) p₁′))


---------------------------------------------------------------------------------------------------------------
--
-- BS-H is reflexive

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ (var)    = var
refl-⇓′ (app p₁) = app (BS-CBN.refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → HNF e → e ⇓ e
refl-⇓ (lam p) = lam (refl-⇓ p)
refl-⇓ (hnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------
