---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-HS where

open import Semantics-SmallStep
open HS public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ { (_ , ()) }
nrf←naxnf (app p₁) = λ { (_ , app₁ r₁)    → (_ , r₁) ↯ nrf←naxnf p₁
                        ; (_ , applam p₁′) → case p₁ of λ ()
                        }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←hnf p }
nrf←hnf (hnf p) = nrf←naxnf p

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)         (lam r′)         = lam & det-⇒ r r′
det-⇒ (app₁ r₁)       (app₁ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ (lam r₁)) (applam p₁′)     = (_ , r₁) ↯ nrf←hnf p₁′
det-⇒ (applam p₁)     (app₁ (lam r₁′)) = (_ , r₁′) ↯ nrf←hnf p₁
det-⇒ (applam p₁)     (applam p₁′)     = refl


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app p₁) (app₁ r₁)    = (_ , r₁) ↯ nrf←naxnf p₁
naxnf-⇒ (app ()) (applam p₁′)

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* = map app₁

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → HNF e₁ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₁ = applam p₁ ◅ ε


---------------------------------------------------------------------------------------------------------------

bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
bs-lam = lam*

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} →
            e₁ ⇒* lam e₁′ → HNF (lam e₁′) → e₁′ [ e₂ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ (lam p₁′) rs = app₁* rs₁ ◅◅ applam* p₁′ ◅◅ rs
bs-applam rs₁ (hnf ())  rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
bs-app = app₁*


---------------------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------------------
