---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HNO₂

module 2-8-2-Properties-SmallStep-HNO₂ where

open import 1-3-Semantics-SmallStep
open HNO₂ public
import 2-6-Properties-SmallStep-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam₊ p′ r) → (_ , r) ↯ nrf←nf p
                      }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (_ , app₁₊ p₁′ r₁)     → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂₋ p₁′ ¬p₂ r₂) → (_ , r₂) ↯ HS.nrf←hnf (hnf←nf p₂)
                            ; (_ , app₂₊ p₁′ p₂′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ is unique

uniq-⇒ : Unique² _⇒_
uniq-⇒ {e = var _}   ()                ()
uniq-⇒ {e = lam _}   (lam₊ p r)        (lam₊ p′ r′)         = lam₊ & uniq-hnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app₁₊ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app₂₋ & uniq-nanf p₁ p₁′ ⊗ uniq-¬hnf ¬p₂ ¬p₂′
                                                                     ⊗ HS.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app₂₊ & uniq-nanf p₁ p₁′ ⊗ uniq-hnf p₂ p₂′
                                                                     ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam₊ p r)        (lam₊ p′ r′)         = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ HS.det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ preserves HNF and goes from HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂₋ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂₊ p₁′ p₂ r₂)  = app p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → HNF e′
hnf-⇒ (lam₊ p r)        = lam (hnf-⇒ r)
hnf-⇒ (app₁₊ p₁ r₁)     = hnf (app (naxnf-⇒ p₁ r₁))
hnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = hnf (app (naxnf←nanf p₁))
hnf-⇒ (app₂₊ p₁ ¬p₂ r₂) = hnf (app (naxnf←nanf p₁))

rev-hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → HNF e
rev-hnf-⇒ (lam₊ p r)        = lam p
rev-hnf-⇒ (app₁₊ p₁ r₁)     = hnf (app p₁)
rev-hnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = hnf (app (naxnf←nanf p₁))
rev-hnf-⇒ (app₂₊ p₁ p₂ r₂)  = hnf (app (naxnf←nanf p₁))


---------------------------------------------------------------------------------------------------------------
