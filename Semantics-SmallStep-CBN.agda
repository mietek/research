---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-CBN where

open import Semantics-SmallStep
open CBN public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
nrf←nanf var         = λ { (_ , ()) }
nrf←nanf (app p₁ p₂) = λ { (_ , applam)  → case p₁ of λ ()
                          ; (_ , app₁ r₁) → (_ , r₁) ↯ nrf←nanf p₁
                          }

nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
nrf←nf (lam p) = λ { (_ , ()) }
nrf←nf (nf p)  = nrf←nanf p

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ { (_ , ()) }
nrf←naxnf (app p₁) = λ { (_ , applam)  → case p₁ of λ ()
                        ; (_ , app₁ r₁) → (_ , r₁) ↯ nrf←naxnf p₁
                        }

nrf←whnf : ∀ {n} {e : Tm n} → WHNF e → NRF e
nrf←whnf lam      = λ { (_ , ()) }
nrf←whnf (whnf p) = nrf←naxnf p

det-⇒ : ∀ {n} {e : Tm n} {e′ e″} → e ⇒ e′ → e ⇒ e″ → e′ ≡ e″
det-⇒ applam    applam    = refl
det-⇒ applam    (app₁ ())
det-⇒ (app₁ ()) applam
det-⇒ (app₁ r)  (app₁ r′) = app & det-⇒ r r′ ⊗ refl


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) applam
nanf-⇒ (app p₁ p₂) (app₁ r₁) = app (nanf-⇒ p₁ r₁) p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) ()
nf-⇒ (nf p)  r  = nf (nanf-⇒ p r)

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ r₁) = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      ()
whnf-⇒ (whnf p) r  = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* = applam ◅ ε

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* = map app₁


---------------------------------------------------------------------------------------------------------------

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} → e₁ ⇒* lam e₁′ → e₁′ [ e₂ ] ⇒* e′ → app e₁ e₂ ⇒* e′
bs-applam rs₁ rs = app₁* rs₁ ◅◅ applam* ◅◅ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
bs-app = app₁*


---------------------------------------------------------------------------------------------------------------

rev-app-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → WHNF e′ →
              (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ e₁′ × NAXNF e₁′ × app e₁′ e₂ ≡ e′)
rev-app-⇒* ε              (whnf (app p₁′)) = inj₂ (_ , ε , p₁′ , refl)
rev-app-⇒* (applam ◅ rs)  p′               = inj₁ (_ , ε , rs)
rev-app-⇒* (app₁ r₁ ◅ rs) p′               with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs′)                  = inj₁ (_ , r₁ ◅ rs₁ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)           = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)

rev-app₀-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → V e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′)
rev-app₀-⇒* ε              ()
rev-app₀-⇒* (applam ◅ rs)  p′ = _ , ε , rs
rev-app₀-⇒* (app₁ r₁ ◅ rs) p′ with rev-app₀-⇒* rs p′
... | _ , rs₁ , rs′            = _ , r₁ ◅ rs₁ , rs′


---------------------------------------------------------------------------------------------------------------
