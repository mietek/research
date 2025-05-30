{-# OPTIONS --sized-types #-}

module A201607.Common.ContextPair where

open import A201607.Common.Context public


-- Context pairs.

infix 4 _⁏_
record Cx² (U V : Set) : Set where
  constructor _⁏_
  field
    int : Cx U
    mod : Cx V

open Cx² public

∅² : ∀ {U V} → Cx² U V
∅² = ∅ ⁏ ∅


-- Context inclusion.

module _ {U V : Set} where
  infix 3 _⊆²_
  _⊆²_ : Cx² U V → Cx² U V → Set
  Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ = Γ ⊆ Γ′ × Δ ⊆ Δ′

  refl⊆² : ∀ {Π} → Π ⊆² Π
  refl⊆² = refl⊆ , refl⊆

  trans⊆² : ∀ {Π Π′ Π″} → Π ⊆² Π′ → Π′ ⊆² Π″ → Π ⊆² Π″
  trans⊆² (η , θ) (η′ , θ′) = trans⊆ η η′ , trans⊆ θ θ′

  weak⊆²₁ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊆² Γ , A ⁏ Δ
  weak⊆²₁ = weak⊆ , refl⊆

  weak⊆²₂ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊆² Γ ⁏ Δ , A
  weak⊆²₂ = refl⊆ , weak⊆

  bot⊆² : ∀ {Π} → ∅² ⊆² Π
  bot⊆² = bot⊆ , bot⊆


-- Context concatenation.

module _ {U V : Set} where
  _⧺²_ : Cx² U V → Cx² U V → Cx² U V
  (Γ ⁏ Δ) ⧺² (Γ′ ⁏ Δ′) = Γ ⧺ Γ′ ⁏ Δ ⧺ Δ′

  weak⊆²⧺₁ : ∀ {Π} Π′ → Π ⊆² Π ⧺² Π′
  weak⊆²⧺₁ (Γ′ ⁏ Δ′) = weak⊆⧺₁ Γ′ , weak⊆⧺₁ Δ′

  weak⊆²⧺₂ : ∀ {Π Π′} → Π′ ⊆² Π ⧺² Π′
  weak⊆²⧺₂ = weak⊆⧺₂ , weak⊆⧺₂
