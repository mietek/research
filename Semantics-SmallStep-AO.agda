---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-AO where

open import Semantics-SmallStep
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
                            ; (_ , app₁ p₂′ r₁)    → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ r₂)        → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)            (lam r′)             = lam & det-⇒ r r′
det-⇒ (applam p₁ p₂)     (applam p₁′ p₂′)     = refl
det-⇒ (applam p₁ p₂)     (app₁ p₂′ (lam r₁′)) = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)     (app₂ r₂′)           = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₁ p₂ (lam r₁)) (applam p₁′ p₂′)     = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (app₁ p₂ r₁)       (app₁ p₂′ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₂ r₁)       (app₂ r₂′)           = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₂ r₂)          (applam p₁′ p₂′)     = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ r₂)          (app₁ p₂′ r₁′)       = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ r₂)          (app₂ r₂′)           = app & refl ⊗ det-⇒ r₂ r₂′

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO preserves NF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) (applam p₁′ p₂′)
nanf-⇒ (app p₁ p₂) (app₁ p₂′ r₁)    = app (nanf-⇒ p₁ r₁) p₂′
nanf-⇒ (app p₁ p₂) (app₂ r₂)        = (_ , r₂) ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←nf p
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-AO

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₁ → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₁ p₂ = applam p₁ p₂ ◅ ε

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NF e₂ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* p₁ = map (app₁ p₁)

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* = map app₂


---------------------------------------------------------------------------------------------------------------
