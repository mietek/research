{-# OPTIONS --sized-types #-}

-- TODO
-- Basic Tarski-style semantics, for soundness only.

module A201607.BasicT.Semantics.BasicTarski where

open import A201607.BasicT.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊩ᵅ_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 ⊩_
  ⊩_ : Ty → Set
  ⊩ α P   = ⊩ᵅ P
  ⊩ A ▻ B = ⊩ A → ⊩ B
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙
  ⊩ BOOL  = 𝔹
  ⊩ NAT   = ℕ

  infix 3 ⊩⋆_
  ⊩⋆_ : Cx Ty → Set
  ⊩⋆ ∅     = 𝟙
  ⊩⋆ Ξ , A = ⊩⋆ Ξ × ⊩ A


-- Entailment, or forcing in all models.

infix 3 ⊨_
⊨_ : Ty → Set₁
⊨ A = ∀ {{_ : Model}} → ⊩ A


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 ⊩_⇒_
  ⊩_⇒_ : Cx Ty → Ty → Set
  ⊩ Γ ⇒ A = ⊩⋆ Γ → ⊩ A

  infix 3 ⊩_⇒⋆_
  ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set
  ⊩ Γ ⇒⋆ Ξ = ⊩⋆ Γ → ⊩⋆ Ξ


-- Entailment, or forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Ξ = ∀ {{_ : Model}} → ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} → A ∈ Γ → ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} → ⊩ Γ , A ⇒ B → ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ f γ = λ a → f (γ , a)

  _⟦$⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ $ g γ

  ⟦S⟧ : ∀ {A B C Γ} → ⊩ Γ ⇒ A ▻ B ▻ C → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ C
  ⟦S⟧ f g a γ = S (f γ) (g γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B → ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
