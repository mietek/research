---------------------------------------------------------------------------------------------------------------

module 1-1-Syntax-Terms where

open import 1-0-Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- Terms

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
                                 ; (suc x) → suc (ρ x)
                                 })
ren (app e₁ e₂) ρ = app (ren e₁ ρ) (ren e₂ ρ)

sub : ∀ {n k} → Tm n → (Fin n → Tm k) → Tm k
sub (var x)     σ = σ x
sub (lam e)     σ = lam (sub e λ { zero    → var zero
                                 ; (suc x) → ren (σ x) suc
                                 })
sub (app e₁ e₂) σ = app (sub e₁ σ) (sub e₂ σ)

_/0 : ∀ {n} → Tm n → Fin (suc n) → Tm n
(s /0) zero    = s
(s /0) (suc x) = var x

{-# DISPLAY _/0 e = e #-}

infix 50 _[_]
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ s ] = sub t (s /0)

{-# DISPLAY sub e σ = e [ σ ] #-}


---------------------------------------------------------------------------------------------------------------
--
-- Equipment for small-step reduction

Deterministic : ∀ {a ℓ} {A : Set a} → Pred (Rel A ℓ) _
Deterministic R = ∀ {x y₁ y₂} → R x y₁ → R x y₂ → y₁ ≡ y₂

Confluent : ∀ {a ℓ} {A : Set a} → Pred (Rel A ℓ) _
Confluent R = ∀ {x y₁ y₂} → (R *) x y₁ → (R *) x y₂ →
              (∃ λ z → (R *) y₁ z × (R *) y₂ z)

Deterministic′ : Pred (∀ {n} → Rel₀ (Tm n)) _
Deterministic′ _⇒_ = ∀ {n} → Deterministic (_⇒_ {n})

Confluent′ : Pred (∀ {n} → Rel₀ (Tm n)) _
Confluent′ _⇒_ = ∀ {n} → Confluent (_⇒_ {n})

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
    {-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}

module Confluence
    (_⇒_   : ∀ {n} → Rel₀ (Tm n))
    (det-⇒ : Deterministic′ _⇒_)
  where
    conf-⇒ : Confluent′ _⇒_
    conf-⇒ ε        rs′        = _ , rs′ , ε
    conf-⇒ (r ◅ rs) ε          = _ , ε , r ◅ rs
    conf-⇒ (r ◅ rs) (r′ ◅ rs′) with det-⇒ r r′
    ... | refl                  = conf-⇒ rs rs′

module UniquenessOfNonReducibleForms
    (_⇒_   : ∀ {n} → Rel₀ (Tm n))
    (det-⇒ : Deterministic′ _⇒_)
  where
    open NonReducibleForms _⇒_
    open MultiStepReductions _⇒_

    uniq-nrf-⇒ : ∀ {n} {e : Tm n} {e′ e″} → e ⇒* e′ → NRF e′ → e ⇒* e″ → NRF e″ → e′ ≡ e″
    uniq-nrf-⇒ ε        p ε          p′ = refl
    uniq-nrf-⇒ ε        p (r′ ◅ rs′) p′ = (_ , r′) ↯ p
    uniq-nrf-⇒ (r ◅ rs) p ε          p′ = (_ , r) ↯ p′
    uniq-nrf-⇒ (r ◅ rs) p (r′ ◅ rs′) p′ with det-⇒ r r′
    ... | refl                           = uniq-nrf-⇒ rs p rs′ p′


---------------------------------------------------------------------------------------------------------------
