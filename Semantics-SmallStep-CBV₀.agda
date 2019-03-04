---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-CBV₀ where

open import Semantics-SmallStep
open CBV₀ public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

nrf←v : ∀ {n} {e : Tm n} → V e → NRF e
nrf←v lam = λ { (_ , ()) }


---------------------------------------------------------------------------------------------------------------

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

v-⇒ : ∀ {n} {e : Tm n} {e′} → V e → e ⇒ e′ → V e′
v-⇒ lam ()


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
