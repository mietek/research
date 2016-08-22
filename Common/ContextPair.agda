module Common.ContextPair where

open import Common.Context public


-- Context pairs.

infix 4 _⁏_
record Cx² (U : Set) : Set where
  constructor _⁏_
  field
    int : Cx U
    mod : Cx U

open Cx² public

⌀² : ∀ {U} → Cx² U
⌀² = ⌀ ⁏ ⌀


-- Context inclusion.

module _ {U : Set} where
  infix 3 _⊆²_
  _⊆²_ : Cx² U → Cx² U → Set
  Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ = Γ ⊆ Γ′ × Δ ⊆ Δ′

  refl⊆² : ∀ {Π} → Π ⊆² Π
  refl⊆² = refl⊆ , refl⊆

  trans⊆² : ∀ {Π Π′ Π″} → Π ⊆² Π′ → Π′ ⊆² Π″ → Π ⊆² Π″
  trans⊆² (η , θ) (η′ , θ′) = trans⊆ η η′ , trans⊆ θ θ′

  weak⊆²ₗ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊆² Γ , A ⁏ Δ
  weak⊆²ₗ = weak⊆ , refl⊆

  weak⊆²ᵣ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊆² Γ ⁏ Δ , A
  weak⊆²ᵣ = refl⊆ , weak⊆

  bot⊆² : ∀ {Π} → ⌀² ⊆² Π
  bot⊆² = bot⊆ , bot⊆


-- Context concatenation.

module _ {U : Set} where
  _⧺²_ : Cx² U → Cx² U → Cx² U
  (Γ ⁏ Δ) ⧺² (Γ′ ⁏ Δ′) = Γ ⧺ Γ′ ⁏ Δ ⧺ Δ′

  weak⊆²⧺ₗ : ∀ {Π} Π′ → Π ⊆² Π ⧺² Π′
  weak⊆²⧺ₗ (Γ′ ⁏ Δ′) = weak⊆⧺ₗ Γ′ , weak⊆⧺ₗ Δ′

  weak⊆²⧺ᵣ : ∀ {Π Π′} → Π′ ⊆² Π ⧺² Π′
  weak⊆²⧺ᵣ = weak⊆⧺ᵣ , weak⊆⧺ᵣ
