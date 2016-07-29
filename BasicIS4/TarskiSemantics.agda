module BasicIS4.TarskiSemantics where

open import BasicIS4 public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Truth for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public


-- Truth for propositions and contexts, inspired by Gabbay and Nanevski.

module ForcingWithBox (Box : Ty → Set) where
  module _ {{_ : Model}} where
    infix 3 ⊨_
    ⊨_ : Ty → Set
    ⊨ α P   = ⊨ᵅ P
    ⊨ A ▷ B = ⊨ A → ⊨ B
    ⊨ □ A   = Box A × ⊨ A
    ⊨ A ∧ B = ⊨ A × ⊨ B
    ⊨ ⊤    = Top

    infix 3 ⊨⋆_
    ⊨⋆_ : Cx Ty → Set
    ⊨⋆ ⌀     = Top
    ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


  -- Truth in all models.

  infix 3 _ᴹ⊨_
  _ᴹ⊨_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A

  infix 3 _ᴹ⊨⋆_
  _ᴹ⊨⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ᴹ⊨⋆ Π = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨⋆ Π

  infix 3 _⁏_ᴹ⊨_
  _⁏_ᴹ⊨_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨⋆ Δ → ⊨ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
