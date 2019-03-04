---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-CBV₀ where

open import Semantics-SmallStep
open CBV₀ public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

nrf←v : ∀ {n} {e : Tm n} → V e → NRF e
nrf←v lam = λ { (_ , ()) }

det-⇒ : Deterministic′ _⇒_
det-⇒ (app₁ r₁)    (app₁ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)    (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←v p₁′
det-⇒ (app₁ ())    (applam p₂′)
det-⇒ (app₂ p₁ r₂) (app₁ r₁′)     = (_ , r₁′) ↯ nrf←v p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂ p₁ r₂) (applam p₂′)   = (_ , r₂) ↯ nrf←v p₂′
det-⇒ (applam p₂)  (app₁ ())
det-⇒ (applam p₂)  (app₂ p₁′ r₂′) = (_ , r₂′) ↯ nrf←v p₂
det-⇒ (applam p₂)  (applam p₂′)   = refl


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* = map app₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → V e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → V e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₂ = applam p₂ ◅ ε


---------------------------------------------------------------------------------------------------------------

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → e₂ ⇒* e₂′ → V e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* lam rs₂ ◅◅ applam* p₂′ ◅◅ rs


---------------------------------------------------------------------------------------------------------------

rev-app-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → V e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × V e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′)
rev-app-⇒* ε                 ()
rev-app-⇒* (app₁ r₁ ◅ rs)    p′ with rev-app-⇒* rs p′
... | _ , rs₁ , rs₂ , p₂′ , rs′  = _ , r₁ ◅ rs₁ , rs₂ , p₂′ , rs′
rev-app-⇒* (app₂ p₁ r₂ ◅ rs) p′ with rev-app-⇒* rs p′
... | _ , rs₁ , rs₂ , p₂′ , rs′  = _ , rs₁ , r₂ ◅ rs₂ , p₂′ , rs′
rev-app-⇒* (applam p₂ ◅ rs)  p′ = _ , ε , ε , p₂ , rs


---------------------------------------------------------------------------------------------------------------
