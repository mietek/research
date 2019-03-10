---------------------------------------------------------------------------------------------------------------

module 1-1-Syntax-Terms where

open import 0-1-Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- Well-scoped terms

data Tm (n : Nat) : Set where
  var : Fin n → Tm n
  lam : Tm (suc n) → Tm n
  app : Tm n → Tm n → Tm n

open import 0-2-GenericEquipment Tm public


---------------------------------------------------------------------------------------------------------------
--
-- Renaming and substitution

ren : ∀ {n k} → Tm n → (Fin n → Fin k) → Tm k
ren (var x)     ρ = var (ρ x)
ren (lam e)     ρ = lam (ren e λ { zero    → zero
                                 ; (suc x) → suc (ρ x) })
ren (app e₁ e₂) ρ = app (ren e₁ ρ) (ren e₂ ρ)

sub : ∀ {n k} → Tm n → (Fin n → Tm k) → Tm k
sub (var x)     σ = σ x
sub (lam e)     σ = lam (sub e λ { zero    → var zero
                                 ; (suc x) → ren (σ x) suc })
sub (app e₁ e₂) σ = app (sub e₁ σ) (sub e₂ σ)

_/0 : ∀ {n} → Tm n → Fin (suc n) → Tm n
(s /0) zero    = s
(s /0) (suc x) = var x

infix 50 _[_]
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ s ] = sub t (s /0)

{-# DISPLAY _/0 e   = e #-}
{-# DISPLAY sub e σ = e [ σ ] #-}


---------------------------------------------------------------------------------------------------------------
