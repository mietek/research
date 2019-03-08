---------------------------------------------------------------------------------------------------------------

module 1-1-Syntax-Terms where

open import 1-0-Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- Well-scoped terms

data Tm (n : Nat) : Set where
  var : Fin n → Tm n
  lam : Tm (suc n) → Tm n
  app : Tm n → Tm n → Tm n


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
--
-- Properties of predicates and relations on well-scoped terms

module Unary where
  Decidable : Pred (∀ {n} → Pred₀ (Tm n)) _
  Decidable P = ∀ {n} → Relation.Unary.Decidable (P {n})

  Unique : Pred (∀ {n} → Pred₀ (Tm n)) _
  Unique P = ∀ {n} → Relation.Unary.Unique (P {n})

module Binary where
  Unique : Pred (∀ {n} → Rel₀ (Tm n)) _
  Unique R = ∀ {n} → Relation.Binary.Unique (R {n})

  Deterministic : Pred (∀ {n} → Rel₀ (Tm n)) _
  Deterministic R = ∀ {n} → Relation.Binary.Deterministic (R {n})

  UniqueTo : (∀ {n} → Pred₀ (Tm n)) → Pred (∀ {n} → Rel₀ (Tm n)) _
  UniqueTo P R = ∀ {n} → Relation.Binary.UniqueTo (P {n}) (R {n})

  Confluent : Pred (∀ {n} → Rel₀ (Tm n)) _
  Confluent R = ∀ {n} → Relation.Binary.Confluent (R {n})


---------------------------------------------------------------------------------------------------------------
--
-- Generic equipment for small-step reduction

module NonReducibleForms
    (_⇒_ : ∀ {n} → Rel₀ (Tm n))
  where
    NRF : ∀ {n} → Pred₀ (Tm n)
    NRF e = ¬ (∃ λ e′ → e ⇒ e′)

module MultiStepReductions
    (_⇒_ : ∀ {n} → Rel₀ (Tm n))
  where
    _⇒*⟨_⟩_ : ∀ {n} → Tm n → Size → Tm n → Set₀
    e ⇒*⟨ i ⟩ e′ = (_⇒_ *⟨ i ⟩) e e′

    _⇒*_ : ∀ {n} → Rel₀ (Tm n)
    e ⇒* e′ = e ⇒*⟨ ∞ ⟩ e′

    {-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
    {-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
    {-# DISPLAY _* _⇒_ e e′      = e ⇒* e′ #-}

module Confluence
    (_⇒_   : ∀ {n} → Rel₀ (Tm n))
    (det-⇒ : Binary.Deterministic _⇒_)
  where
    open MultiStepReductions _⇒_

    conf-⇒ : Binary.Confluent _⇒_
    conf-⇒ ε        rs′        = _ , rs′ , ε
    conf-⇒ (r ◅ rs) ε          = _ , ε , r ◅ rs
    conf-⇒ (r ◅ rs) (r′ ◅ rs′) with det-⇒ r r′
    ... | refl                  = conf-⇒ rs rs′

module UniquenessOfNonReducibleForms
    (_⇒_   : ∀ {n} → Rel₀ (Tm n))
    (det-⇒ : Binary.Deterministic _⇒_)
  where
    open NonReducibleForms _⇒_
    open MultiStepReductions _⇒_

    uniq-nrf-⇒ : Binary.UniqueTo NRF _⇒*_
    uniq-nrf-⇒ ε        p ε          p′ = refl
    uniq-nrf-⇒ ε        p (r′ ◅ rs′) p′ = (_ , r′) ↯ p
    uniq-nrf-⇒ (r ◅ rs) p ε          p′ = (_ , r) ↯ p′
    uniq-nrf-⇒ (r ◅ rs) p (r′ ◅ rs′) p′ with det-⇒ r r′
    ... | refl                           = uniq-nrf-⇒ rs p rs′ p′


---------------------------------------------------------------------------------------------------------------
