---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-AO

module 2-4-Properties-SmallStep-AO where

open import 1-3-Semantics-SmallStep
open AO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam p₁′ p₂′) → case p₁ of λ ()
                            ; (_ , app₁ r₁)        → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁ r₂)     → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)            (lam r′)             = lam & det-⇒ r r′
det-⇒ (applam p₁ p₂)     (applam p₁′ p₂′)     = refl
det-⇒ (applam p₁ p₂)     (app₁ (lam r₁′))     = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)     (app₂ p₁′ r₂′)       = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₁ (lam r₁))    (applam p₁′ p₂′)     = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (app₁ r₁)          (app₁ r₁′)           = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)          (app₂ p₁′ r₂′)       = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (app₂ p₁ r₂)       (applam p₁′ p₂′)     = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ p₁ r₂)       (app₁ r₁′)           = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (app₂ p₁ r₂)       (app₂ p₁′ r₂′)       = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO preserves NF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) (applam p₁′ p₂′)
nanf-⇒ (app p₁ p₂) (app₁ r₁)        = app (nanf-⇒ p₁ r₁) p₂
nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂)    = (_ , r₂) ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←nf p
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
