---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-NO₂ where

open import Semantics-SmallStep
import Semantics-SmallStep-CBN as SS-CBN
open NO₂ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam₋ ¬p r) → whnf←nf p ↯ ¬p
                      ; (_ , lam₊ p′ r) → (_ , r) ↯ nrf←nf p
                      }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , app₁₊ p₁′ r₁)     → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂₋ p₁′ ¬p₂ r₂) → (_ , r₂) ↯ SS-CBN.nrf←whnf (whnf←nf p₂)
                            ; (_ , app₂₊ p₁′ p₂′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam & SS-CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
det-⇒ (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
det-⇒ (lam₊ p r)        (lam₊ p′ r′)         = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ SS-CBN.det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app & refl ⊗ det-⇒ r₂ r₂′

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ preserves NF and WHNF, and goes from WHNF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app p₁ p₂) (app₁₊ p₁′ r₂)     = app (nanf-⇒ p₁ r₂) p₂
nanf-⇒ (app p₁ p₂) (app₂₋ p₁′ ¬p₂ r₂) = whnf←nf p₂ ↯ ¬p₂
nanf-⇒ (app p₁ p₂) (app₂₊ p₁′ p₂′ r₂) = (_ , r₂) ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam₋ ¬p r) = whnf←nf p ↯ ¬p
nf-⇒ (lam p) (lam₊ p′ r) = (_ , r) ↯ nrf←nf p
nf-⇒ (nf p)  r           = nf (nanf-⇒ p r)

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
--
-- Extras for BS-NO₂

cbn-app₂ : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ CBN.⇒ e₂′ → app e₁ e₂ ⇒ app e₁ e₂′
cbn-app₂ p₁ r₂ with whnf? _
... | no ¬p₂   = app₂₋ p₁ ¬p₂ r₂
... | yes p₂   = (_ , r₂) ↯ SS-CBN.nrf←whnf p₂

app₂ : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒ e₂′ → app e₁ e₂ ⇒ app e₁ e₂′
app₂ p₁ r = app₂₊ p₁ (rev-whnf-⇒ r) r

cbn-lam : ∀ {n} {e : Tm (suc n)} {e′} → e CBN.⇒ e′ → lam e ⇒ lam e′
cbn-lam r   with whnf? _
... | no ¬p = lam₋ ¬p r
... | yes p = (_ , r) ↯ SS-CBN.nrf←whnf p

lam′ : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒ e′ → lam e ⇒ lam e′
lam′ r = lam₊ (rev-whnf-⇒ r) r


---------------------------------------------------------------------------------------------------------------
--
-- More extras for BS-NO₂

cbn-app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ SS-CBN.⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
cbn-app₂* p₁ = map (cbn-app₂ p₁)

app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁₊* p₁ ε          = ε
app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

cbn-lam* : ∀ {n} {e : Tm (suc n)} {e′} → e SS-CBN.⇒* e′ → lam e ⇒* lam e′
cbn-lam* = map cbn-lam

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam′


---------------------------------------------------------------------------------------------------------------
