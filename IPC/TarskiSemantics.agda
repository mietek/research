module IPC.TarskiSemantics where

open import IPC public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Satisfaction for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public




module NaturalSemantics where


  -- Satisfaction in a particular model.

  infix 3 ⊨_
  ⊨_ : ∀ {{_ : Model}} → Ty → Set
  ⊨ α P   = ⊨ᵅ P
  ⊨ A ▻ B = ⊨ A → ⊨ B
  ⊨ A ∧ B = ⊨ A × ⊨ B
  ⊨ ⊤    = 𝟙
  ⊨ ⊥    = 𝟘
  ⊨ A ∨ B = ⊨ A ⊎ ⊨ B

  infix 3 ⊨⋆_
  ⊨⋆_ : ∀ {{_ : Model}} → Cx Ty → Set
  ⊨⋆ ⌀     = 𝟙
  ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


  -- Satisfaction in all models.

  infix 3 ᴹ⊨_
  ᴹ⊨_ : Ty → Set₁
  ᴹ⊨ A = ∀ {{_ : Model}} → ⊨ A

  infix 3 _ᴹ⊨_
  _ᴹ⊨_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ




-- Satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSemantics (Syntax : Ty → Set) where


  -- Satisfaction in a particular model.

  infix 3 ⊨_
  ⊨_ : ∀ {{_ : Model}} → Ty → Set
  ⊨ α P   = Syntax (α P) × ⊨ᵅ P
  ⊨ A ▻ B = Syntax (A ▻ B) × (⊨ A → ⊨ B)
  ⊨ A ∧ B = ⊨ A × ⊨ B
  ⊨ ⊤    = 𝟙
  ⊨ ⊥    = 𝟘
  ⊨ A ∨ B = ⊨ A ⊎ ⊨ B

  infix 3 ⊨⋆_
  ⊨⋆_ : ∀ {{_ : Model}} → Cx Ty → Set
  ⊨⋆ ⌀     = 𝟙
  ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


  -- Satisfaction in all models.

  infix 3 ᴹ⊨_
  ᴹ⊨_ : Ty → Set₁
  ᴹ⊨ A = ∀ {{_ : Model}} → ⊨ A

  infix 3 _ᴹ⊨_
  _ᴹ⊨_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A


  -- Additional useful equipment.

  _$ˢ_ : ∀ {{_ : Model}} {A B} → Syntax (A ▻ B) × (⊨ A → ⊨ B) → ⊨ A → ⊨ B
  (t , f) $ˢ a = f a

  elim⊎ˢ : ∀ {{_ : Model}} {A B C}
           → ⊨ A ⊎ ⊨ B
           → Syntax (A ▻ C) × (⊨ A → ⊨ C)
           → Syntax (B ▻ C) × (⊨ B → ⊨ C)
           → ⊨ C
  elim⊎ˢ (ι₁ a) (u , f) (v , g) = f a
  elim⊎ˢ (ι₂ b) (u , f) (v , g) = g b

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
