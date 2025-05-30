{-# OPTIONS --sized-types #-}

module A201607.Common.Semantics where

open import A201607.Common.Context public


-- Special products for glueing.

infix 5 _⅋_
record Glue (Syn : Set) (Sem : Set) : Set where
  constructor _⅋_
  field
    syn : Syn
    sem : Sem

open Glue public


-- Contexts as concrete worlds.

module ConcreteWorlds (U : Set) where
  record World : Set where
    constructor wrap
    field
      Γ : Cx U

  unwrap : World → Cx U
  unwrap (wrap Γ) = Γ

  data _≤_ : World → World → Set where
    wrap : ∀ {Γ Γ′} → Γ ⊆ Γ′ → wrap Γ ≤ wrap Γ′

  unwrap≤ : ∀ {Γ Γ′} → wrap Γ ≤ wrap Γ′ → Γ ⊆ Γ′
  unwrap≤ (wrap η) = η

  refl≤ : ∀ {w} → w ≤ w
  refl≤ = wrap refl⊆

  trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
  trans≤ (wrap η) (wrap η′) = wrap (trans⊆ η η′)

  weak≤ : ∀ {A w} → w ≤ wrap (unwrap w , A)
  weak≤ = wrap weak⊆
