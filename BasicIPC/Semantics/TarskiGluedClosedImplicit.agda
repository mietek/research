-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Tarski-style semantics with glueing for α and ▻, after Coquand-Dybjer.
-- Implicit closed syntax.

module A201607.BasicIPC.Semantics.TarskiGluedClosedImplicit where

open import A201607.BasicIPC.Syntax.Common public
open import A201607.Common.Semantics public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊩ᵅ_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

open Model {{…}} public




module ImplicitSyntax
    ([⊢]_ : Ty → Set)
  where


  -- Forcing in a particular model.

  module _ {{_ : Model}} where
    infix 3 ⊩_
    ⊩_ : Ty → Set
    ⊩ α P   = Glue ([⊢] (α P)) (⊩ᵅ P)
    ⊩ A ▻ B = Glue ([⊢] (A ▻ B)) (⊩ A → ⊩ B)
    ⊩ A ∧ B = ⊩ A × ⊩ B
    ⊩ ⊤    = 𝟙

    infix 3 ⊩⋆_
    ⊩⋆_ : Cx Ty → Set
    ⊩⋆ ∅     = 𝟙
    ⊩⋆ Ξ , A = ⊩⋆ Ξ × ⊩ A


  -- Entailment, or forcing in all models.

  infix 3 ⊨_
  ⊨_ : Ty → Set₁
  ⊨ A = ∀ {{_ : Model}} → ⊩ A


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B} → ⊩ A ▻ B → ⊩ A → ⊩ B
    s ⟪$⟫ a = sem s a

    ⟪S⟫ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ A ▻ B → ⊩ A → ⊩ C
    ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)


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

    ⟦λ⟧ : ∀ {A B Γ} → [⊢] (A ▻ B) → ⊩ Γ , A ⇒ B → ⊩ Γ ⇒ A ▻ B
    ⟦λ⟧ t s γ = t ⅋ λ a → s (γ , a)

    _⟦$⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B
    (s₁ ⟦$⟧ s₂) γ = s₁ γ ⟪$⟫ s₂ γ

    ⟦S⟧ : ∀ {A B C Γ} → ⊩ Γ ⇒ A ▻ B ▻ C → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ C
    ⟦S⟧ s₁ s₂ a γ = ⟪S⟫ (s₁ γ) (s₂ γ) (a γ)

    _⟦,⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B → ⊩ Γ ⇒ A ∧ B
    (a ⟦,⟧ b) γ = a γ , b γ

    ⟦π₁⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ A
    ⟦π₁⟧ s γ = π₁ (s γ)

    ⟦π₂⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ B
    ⟦π₂⟧ s γ = π₂ (s γ)
