---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HS

module 2-6-Properties-SmallStep-HS where

open import 1-3-Semantics-SmallStep
open HS public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS does not reduce HNF

open NonReducibleForms _⇒_ public

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ { (_ , ()) }
nrf←naxnf (app p₁) = λ { (_ , applam p₁′) → case p₁ of λ ()
                        ; (_ , app₁ r₁)    → (_ , r₁) ↯ nrf←naxnf p₁
                        }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←hnf p }
nrf←hnf (hnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)         (lam r′)         = lam & det-⇒ r r′
det-⇒ (applam p₁)     (applam p₁′)     = refl
det-⇒ (applam p₁)     (app₁ (lam r₁′)) = (_ , r₁′) ↯ nrf←hnf p₁
det-⇒ (app₁ (lam r₁)) (applam p₁′)     = (_ , r₁) ↯ nrf←hnf p₁′
det-⇒ (app₁ r₁)       (app₁ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS preserves HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) (applam p₁′)
naxnf-⇒ (app p₁) (app₁ r₁)    = (_ , r₁) ↯ nrf←naxnf p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
