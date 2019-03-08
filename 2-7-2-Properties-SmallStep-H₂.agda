---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H₂

module 2-7-2-Properties-SmallStep-H₂ where

open import 1-3-Semantics-SmallStep
open H₂ public
import 2-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ does not reduce HNF

open NonReducibleForms _⇒_ public

mutual
  nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
  nrf←hnf (lam p) = λ { (_ , lam₋ ¬p r) → whnf←hnf p ↯ ¬p
                       ; (_ , lam₊ p′ r) → (_ , r) ↯ nrf←hnf p
                       }
  nrf←hnf (hnf p) = nrf←naxnf p

  nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
  nrf←naxnf var      = λ { (_ , ()) }
  nrf←naxnf (app p₁) = λ { (_ , app₁₊ p₁′ r₁) → (_ , r₁) ↯ nrf←naxnf p₁
                          }


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is unique

uniq-⇒ : Unique² _⇒_
uniq-⇒ {e = var _}   ()            ()
uniq-⇒ {e = lam _}   (lam₋ ¬p r)   (lam₋ ¬p′ r′)   = lam₋ & uniq-¬whnf ¬p ¬p′  ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _}   (lam₋ ¬p r)   (lam₊ p′ r′)    = p′ ↯ ¬p
uniq-⇒ {e = lam _}   (lam₊ p r)    (lam₋ ¬p′ r′)   = p ↯ ¬p′
uniq-⇒ {e = lam _}   (lam₊ p r)    (lam₊ p′ r′)    = lam₊ & uniq-whnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁) (app₁₊ p₁′ r₁′) = app₁₊ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is deterministic, confluent, and has unique hn-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam₋ ¬p r)   (lam₋ ¬p′ r′)   = lam & CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)   (lam₊ p′ r′)    = p′ ↯ ¬p
det-⇒ (lam₊ p r)    (lam₋ ¬p′ r′)   = p ↯ ¬p′
det-⇒ (lam₊ p r)    (lam₊ p′ r′)    = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁) (app₁₊ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (lam₋ ¬p r)   = lam
whnf-⇒ (lam₊ p r)    = lam
whnf-⇒ (app₁₊ p₁ r₁) = whnf (app (naxnf-⇒ p₁ r₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (lam₋ ¬p r)   = lam
rev-whnf-⇒ (lam₊ p r)    = lam
rev-whnf-⇒ (app₁₊ p₁ r₁) = whnf (app p₁)


---------------------------------------------------------------------------------------------------------------
