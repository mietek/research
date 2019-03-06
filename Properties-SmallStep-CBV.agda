---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-CBV

module Properties-SmallStep-CBV where

open import Semantics-SmallStep
open CBV public


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV does not reduce WNF

open NonReducibleForms _⇒_ public

mutual
  nrf←wnf : ∀ {n} {e : Tm n} → WNF e → NRF e
  nrf←wnf lam     = λ { (_ , ()) }
  nrf←wnf (wnf p) = nrf←nawnf p

  nrf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NRF e
  nrf←nawnf var         = λ { (_ , ()) }
  nrf←nawnf (app p₁ p₂) = λ { (_ , applam p₂′)   → case p₁ of λ ()
                             ; (_ , app₁ r₁′)     → (_ , r₁′) ↯ nrf←nawnf p₁
                             ; (_ , app₂ p₁′ r₂′) → (_ , r₂′) ↯ nrf←wnf p₂
                             }


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (applam p₂)  (applam p₂′)   = refl
det-⇒ (applam p₂)  (app₁ ())
det-⇒ (applam p₂)  (app₂ p₁′ r₂′) = (_ , r₂′) ↯ nrf←wnf p₂
det-⇒ (app₁ ())    (applam p₂′)
det-⇒ (app₁ r₁)    (app₁ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)    (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←wnf p₁′
det-⇒ (app₂ p₁ r₂) (applam p₂′)   = (_ , r₂) ↯ nrf←wnf p₂′
det-⇒ (app₂ p₁ r₂) (app₁ r₁′)     = (_ , r₁′) ↯ nrf←wnf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV preserves WNF

nawnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇒ e′ → NAWNF e′
nawnf-⇒ var       ()
nawnf-⇒ (app () p₂) (applam p₂′)
nawnf-⇒ (app p₁ p₂) (app₁ r₁)     = app (nawnf-⇒ p₁ r₁) p₂
nawnf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = (_ , r₂) ↯ nrf←wnf p₂

wnf-⇒ : ∀ {n} {e : Tm n} {e′} → WNF e → e ⇒ e′ → WNF e′
wnf-⇒ lam     ()
wnf-⇒ (wnf p) r  = wnf (nawnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
