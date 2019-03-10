---------------------------------------------------------------------------------------------------------------

module 1-1-Syntax-Terms where

open import 0-1-Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- Well-scoped nameless terms

data Tm (n : Nat) : Set where
  var : Fin n → Tm n
  lam : Tm (suc n) → Tm n
  app : Tm n → Tm n → Tm n

open import 0-2-GenericEquipment Tm public


---------------------------------------------------------------------------------------------------------------
--
-- Simultaneous substitution

sren : ∀ {n k} → Tm n → (Fin n → Fin k) → Tm k
sren (var x)     ρ = var (ρ x)
sren (lam e)     ρ = lam (sren e λ { zero    → zero
                                   ; (suc x) → suc (ρ x) })
sren (app e₁ e₂) ρ = app (sren e₁ ρ) (sren e₂ ρ)

ssub : ∀ {n k} → Tm n → (Fin n → Tm k) → Tm k
ssub (var x)     σ = σ x
ssub (lam e)     σ = lam (ssub e λ { zero    → var zero
                                   ; (suc x) → sren (σ x) suc })
ssub (app e₁ e₂) σ = app (ssub e₁ σ) (ssub e₂ σ)


---------------------------------------------------------------------------------------------------------------
--
-- Substitution of topmost variable

_/0 : ∀ {n} → Tm n → Fin (suc n) → Tm n
(s /0) zero    = s
(s /0) (suc x) = var x

infix 50 _[_]
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ s ] = ssub t (s /0)

{-# DISPLAY _/0 e       = e #-}
{-# DISPLAY ssub e σ = e [ σ ] #-}


---------------------------------------------------------------------------------------------------------------
