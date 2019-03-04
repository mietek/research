---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-H where

open import Semantics-BigStep
open H public
import Semantics-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-H goes to HNF

hnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → HNF e′
hnf-⇓ var           = hnf var
hnf-⇓ (lam r)       = lam (hnf-⇓ r)
hnf-⇓ (applam r₁ r) = hnf-⇓ r
hnf-⇓ (app r₁ q)    = hnf (app (naxnf←whnf (BS-CBN.whnf-⇓ r₁) q))


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
--
-- TODO: BS-H implies SS-H


---------------------------------------------------------------------------------------------------------------
--
-- TODO: SS-H to HNF implies BS-H


---------------------------------------------------------------------------------------------------------------
--
-- TODO: BS-H and SS-H to HNF coincide

-- bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × HNF e′)
-- bs↔ss = (λ r → ss←bs r , hnf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
