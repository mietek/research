---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO₂

module 2-2-2-Properties-SmallStep-NO₂ where

open import 1-3-Semantics-SmallStep
open NO₂ public
import 2-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam₋ ¬p r) → whnf←nf p ↯ ¬p
                      ; (_ , lam₊ p′ r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (_ , app₁₊ p₁′ r₁)     → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂₋ p₁′ ¬p₂ r₂) → (_ , r₂) ↯ CBN.nrf←whnf (whnf←nf p₂)
                            ; (_ , app₂₊ p₁′ p₂′ r₂) → (_ , r₂) ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is unique

uniq-⇒ : Unique² _⇒_
uniq-⇒ {e = var _}   ()                ()
uniq-⇒ {e = lam _}   (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam₋ & uniq-¬whnf ¬p ¬p′  ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _}   (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
uniq-⇒ {e = lam _}   (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
uniq-⇒ {e = lam _}   (lam₊ p r)        (lam₊ p′ r′)         = lam₊ & uniq-whnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app₁₊ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app₂₋ & uniq-nanf p₁ p₁′ ⊗ uniq-¬whnf ¬p₂ ¬p₂′
                                                                     ⊗ CBN.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app₂₊ & uniq-nanf p₁ p₁′ ⊗ uniq-whnf p₂ p₂′
                                                                     ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam & CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
det-⇒ (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
det-⇒ (lam₊ p r)        (lam₊ p′ r′)         = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ CBN.det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂₋ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂₊ p₁′ p₂ r₂)  = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (lam₋ ¬p r)       = lam
whnf-⇒ (lam₊ p r)        = lam
whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app (naxnf-⇒ p₁ r₁))
whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
whnf-⇒ (app₂₊ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (lam₋ ¬p r)       = lam
rev-whnf-⇒ (lam₊ p r)        = lam
rev-whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app p₁)
rev-whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
rev-whnf-⇒ (app₂₊ p₁ p₂ r₂)  = whnf (app (naxnf←nanf p₁))


---------------------------------------------------------------------------------------------------------------
