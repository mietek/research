---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HAO

module 2-5-1-Properties-SmallStep-HAO where

open import 1-3-Semantics-SmallStep
open HAO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → case p of
                      λ { (nf (app p₁ p₂)) → (_ , r) ↯ nrf←nf p₂ } }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam p₁′ p₂′) → case p₁ of λ ()
                            ; (_ , app₁ p₁′ r₁ p₂′)    → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ r₂)        → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)               (lam r′)                = lam & (app & refl ⊗ det-⇒ r r′)
det-⇒ (applam p₁ p₂)        (applam p₁′ p₂′)        = refl
det-⇒ (applam p₁ p₂)        (app₁ () (lam r₁′) p₂′)
det-⇒ (applam p₁ p₂)        (app₂ r₂′)              = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₁ () (lam r₁) p₂) (applam p₁′ p₂′)
det-⇒ (app₁ p₁ r₁ p₂)       (app₁ p₁′ r₁′ p₂′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁ p₂)       (app₂ r₂′)              = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₂ r₂)             (applam p₁′ p₂′)        = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ r₂)             (app₁ p₁′ r₁′ p₂′)      = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ r₂)             (app₂ r₂′)              = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO preserves NF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) (applam p₁′ p₂′)
nanf-⇒ (app p₁ p₂) (app₁ p₁′ r₁ p₂′) = app (nanf-⇒ p₁ r₁) p₂′
nanf-⇒ (app p₁ p₂) (app₂ r₂)         = (_ , r₂) ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = case p of λ { (nf (app p₁ p₂)) → (_ , r) ↯ nrf←nf p₂ }
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
