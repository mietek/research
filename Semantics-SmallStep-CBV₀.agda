---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-CBV₀ where

open import Semantics-SmallStep
open CBV₀ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV₀ does not reduce V

open NonReducibleForms _⇒_ public

nrf←v : ∀ {n} {e : Tm n} → V e → NRF e
nrf←v lam = λ { (_ , ()) }


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV₀ is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (applam p₂)  (applam p₂′)   = refl
det-⇒ (applam p₂)  (app₁ ())
det-⇒ (applam p₂)  (app₂ p₁′ r₂′) = (_ , r₂′) ↯ nrf←v p₂
det-⇒ (app₁ ())    (applam p₂′)
det-⇒ (app₁ r₁)    (app₁ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)    (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←v p₁′
det-⇒ (app₂ p₁ r₂) (applam p₂′)   = (_ , r₂) ↯ nrf←v p₂′
det-⇒ (app₂ p₁ r₂) (app₁ r₁′)     = (_ , r₁′) ↯ nrf←v p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV₀ preserves V

v-⇒ : ∀ {n} {e : Tm n} {e′} → V e → e ⇒ e′ → V e′
v-⇒ lam ()


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-CBV₀

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → V e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₂ = applam p₂ ◅ ε

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* = map app₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → V e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)


---------------------------------------------------------------------------------------------------------------
