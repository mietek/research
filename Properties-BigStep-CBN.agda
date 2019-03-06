---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-CBN

module Properties-BigStep-CBN where

open import Semantics-BigStep
open CBN public


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN goes to WHNF

whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e′
whnf-⇓ var           = whnf var
whnf-⇓ lam           = lam
whnf-⇓ (applam r₁ r) = whnf-⇓ r
whnf-⇓ (app r₁ q₁′)  = whnf (app (naxnf←whnf (whnf-⇓ r₁) q₁′))


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN is reflexive

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var      = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → WHNF e → e ⇓ e
refl-⇓ lam      = lam
refl-⇓ (whnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------
