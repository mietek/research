---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO

module 2-2-1-Properties-SmallStep-NO where

open import 1-3-Semantics-SmallStep
open NO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO contains SS-CBN

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁ app applam
cbn-app₁ (CBN.app₁ r₁) = app₁ app (cbn-app₁ r₁)

no←cbn : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
no←cbn CBN.applam    = applam
no←cbn (CBN.app₁ r₁) = cbn-app₁ r₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO contains SS-NO₂

app₁₊ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₊ var      r₁ = app₁ var r₁
app₁₊ (app p₁) r₁ = app₁ app r₁

no←no₂ : ∀ {n} {e : Tm n} {e′} → e NO₂.⇒ e′ → e ⇒ e′
no←no₂ (NO₂.lam₋ ¬p r)       = lam (no←cbn r)
no←no₂ (NO₂.lam₊ p r)        = lam (no←no₂ r)
no←no₂ (NO₂.app₁₊ p₁ r₁)     = app₁₊ p₁ (no←no₂ r₁)
no←no₂ (NO₂.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (no←cbn r₂)
no←no₂ (NO₂.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (no←no₂ r₂)


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
