---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-CBV where

open import Semantics-SmallStep
open CBV public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

mutual
  nrf←wnf : ∀ {n} {e : Tm n} → WNF e → NRF e
  nrf←wnf lam     = λ { (_ , ()) }
  nrf←wnf (wnf p) = nrf←nawnf p

  nrf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NRF e
  nrf←nawnf var         = λ { (_ , ()) }
  nrf←nawnf (app p₁ p₂) = λ { (_ , app₁ r₁′)     → (_ , r₁′) ↯ nrf←nawnf p₁
                             ; (_ , app₂ p₁′ r₂′) → (_ , r₂′) ↯ nrf←wnf p₂
                             ; (_ , applam p₂′)   → case p₁ of λ ()
                             }

det-⇒ : ∀ {n} {e : Tm n} {e′ e″} → e ⇒ e′ → e ⇒ e″ → e′ ≡ e″
det-⇒ (app₁ r₁)    (app₁ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)    (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←wnf p₁′
det-⇒ (app₁ ())    (applam p₂′)
det-⇒ (app₂ p₁ r₂) (app₁ r₁′)     = (_ , r₁′) ↯ nrf←wnf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂ p₁ r₂) (applam p₂′)   = (_ , r₂) ↯ nrf←wnf p₂′
det-⇒ (applam p₂)  (app₁ ())
det-⇒ (applam p₂)  (app₂ p₁′ r₂′) = (_ , r₂′) ↯ nrf←wnf p₂
det-⇒ (applam p₂)  (applam p₂′)   = refl

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* = map app₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → WNF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → WNF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₂ = applam p₂ ◅ ε


---------------------------------------------------------------------------------------------------------------

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → e₂ ⇒* e₂′ → WNF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* lam rs₂ ◅◅ applam* p₂′ ◅◅ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
         e₁ ⇒* e₁′ → WNF e₁′ → e₂ ⇒* e₂′ →
         app e₁ e₂ ⇒* app e₁′ e₂′
bs-app rs₁ p₁′ rs₂ = app₁* rs₁ ◅◅ app₂* p₁′ rs₂


---------------------------------------------------------------------------------------------------------------

rev-app-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → WNF e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NAWNF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × app e₁′ e₂′ ≡ e′)
rev-app-⇒* ε                      (wnf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
rev-app-⇒* (app₁ r ◅ rs)          p′                with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)               = inj₁ (_ , r ◅ rs₁ , rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , r ◅ rs₁ , p₁′ , rs₂ , p₂′ , refl)
rev-app-⇒* (app₂ lam r ◅ rs)      p′                with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)               = inj₁ (_ , rs₁ , r ◅ rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , rs₁ , p₁′ , r ◅ rs₂ , p₂′ , refl)
rev-app-⇒* (app₂ (wnf p₁) r ◅ rs) p′                with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)               = inj₁ (_ , rs₁ , r ◅ rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , rs₁ , p₁′ , r ◅ rs₂ , p₂′ , refl)
rev-app-⇒* (applam p₂ ◅ rs)       p′                = inj₁ (_ , ε , ε , p₂ , rs)


---------------------------------------------------------------------------------------------------------------
