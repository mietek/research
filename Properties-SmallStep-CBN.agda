---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-CBN

module Properties-SmallStep-CBN where

open import Semantics-SmallStep
open CBN public


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN does not reduce WHNF

open NonReducibleForms _⇒_ public

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ { (_ , ()) }
nrf←naxnf (app p₁) = λ { (_ , applam)  → case p₁ of λ ()
                        ; (_ , app₁ r₁) → (_ , r₁) ↯ nrf←naxnf p₁
                        }

nrf←whnf : ∀ {n} {e : Tm n} → WHNF e → NRF e
nrf←whnf lam      = λ { (_ , ()) }
nrf←whnf (whnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ applam    applam    = refl
det-⇒ applam    (app₁ ())
det-⇒ (app₁ ()) applam
det-⇒ (app₁ r)  (app₁ r′) = app & det-⇒ r r′ ⊗ refl

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN preserves WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ r₁) = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      ()
whnf-⇒ (whnf p) r  = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
