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
-- Renaming

Ren : Rel₀ Nat
Ren n k = Fin k → Fin n

keep : ∀ {n k} → Ren n k → Ren (suc n) (suc k)
keep ρ = λ { zero    → zero
           ; (suc x) → suc (ρ x) }

ren : ∀ {n k} → Ren n k → Tm k → Tm n
ren ρ (var x)     = var (ρ x)
ren ρ (lam e)     = lam (ren (keep ρ) e)
ren ρ (app e₁ e₂) = app (ren ρ e₁) (ren ρ e₂)


---------------------------------------------------------------------------------------------------------------
--
-- Substitution

Sub : Rel₀ Nat
Sub n k = Fin k → Tm n

lift : ∀ {n k} → Sub n k → Sub (suc n) (suc k)
lift σ = λ { zero    → var zero
           ; (suc x) → ren suc (σ x) }

sub : ∀ {n k} → Sub n k → Tm k → Tm n
sub σ (var x)     = σ x
sub σ (lam e)     = lam (sub (lift σ) e)
sub σ (app e₁ e₂) = app (sub σ e₁) (sub σ e₂)


---------------------------------------------------------------------------------------------------------------
--
-- Substitution of topmost variable

_/0 : ∀ {n} → Tm n → Sub n (suc n)
(eₛ /0) zero    = eₛ
(eₛ /0) (suc x) = var x

infix 50 _[_]
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
e [ eₛ ] = sub (eₛ /0) e

{-# DISPLAY _/0 e   = e #-}
{-# DISPLAY sub σ e = e [ σ ] #-}


---------------------------------------------------------------------------------------------------------------
