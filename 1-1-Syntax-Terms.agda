---------------------------------------------------------------------------------------------------------------

module A201903.1-1-Syntax-Terms where

open import A201903.0-1-Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- Well-scoped λ-calculus terms, with de Bruijn indices and advisory-only names

data Tm (n : Nat) : Set where
  var : String → Fin n → Tm n
  lam : String → Tm (suc n) → Tm n
  app : Tm n → Tm n → Tm n

open import A201903.0-2-GenericEquipment Tm public


---------------------------------------------------------------------------------------------------------------
--
-- Renaming

Ren : Rel₀ Nat
Ren n k = Fin k → Fin n

keep : ∀ {n k} → Ren n k → Ren (suc n) (suc k)
keep ρ = λ { zero    → zero
           ; (suc x) → suc (ρ x) }

ren : ∀ {n k} → Ren n k → Tm k → Tm n
ren ρ (var s x)   = var s (ρ x)
ren ρ (lam s e)   = lam s (ren (keep ρ) e)
ren ρ (app e₁ e₂) = app (ren ρ e₁) (ren ρ e₂)


---------------------------------------------------------------------------------------------------------------
--
-- Substitution

Sub : Rel₀ Nat
Sub n k = String → Fin k → Tm n

lift : ∀ {n k} → Sub n k → Sub (suc n) (suc k)
lift σ = λ { s zero    → var s zero
           ; s (suc x) → ren suc (σ s x) }

sub : ∀ {n k} → Sub n k → Tm k → Tm n
sub σ (var s x)   = σ s x
sub σ (lam s e)   = lam s (sub (lift σ) e)
sub σ (app e₁ e₂) = app (sub σ e₁) (sub σ e₂)


---------------------------------------------------------------------------------------------------------------
--
-- Substitution of topmost variable

_/0 : ∀ {n} → Tm n → Sub n (suc n)
(eₛ /0) s zero    = eₛ
(eₛ /0) s (suc x) = var s x

infix 50 _[_]
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
e [ eₛ ] = sub (eₛ /0) e

{-# DISPLAY _/0 e   = e #-}
{-# DISPLAY sub σ e = e [ σ ] #-}


---------------------------------------------------------------------------------------------------------------
