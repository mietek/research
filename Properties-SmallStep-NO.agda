---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO

module Properties-SmallStep-NO where

open import Semantics-SmallStep
open NO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam)      → case p₁ of λ ()
                            ; (_ , app₁ p₁′ r₁) → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)      (lam r′)       = lam & det-⇒ r r′
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ applam       (app₂ () r₂′)
det-⇒ (app₁ () r₁) applam
det-⇒ (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁) (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂) applam
det-⇒ (app₂ p₁ r₂) (app₁ p₁′ r₁′) = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO preserves NF and WHNF

mutual
  nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
  nf-⇒ (lam p) (lam r) = lam (nf-⇒ p r)
  nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)

  nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
  nanf-⇒ var         ()
  nanf-⇒ (app () p₂) applam
  nanf-⇒ (app p₁ p₂) (app₁ p₁′ r₁) = app (nanf-⇒ p₁ r₁) p₂
  nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = app p₁′ (nf-⇒ p₂ r₂)

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ p₁′ r₁) = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂ p₁′ r₂) = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      (lam r) = lam
whnf-⇒ (whnf p) r       = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
