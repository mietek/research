module BasicIPC.TarskiSemantics.CoquandDybjer where

open import BasicIPC public
open import BasicIPC.TarskiSemantics using (Model ; ⊨ᵅ_) public


-- Truth with a syntactic component, inspired by Coquand and Dybjer.

module Glueing (Syn : Ty → Set) where
  module _ {{_ : Model}} where
    infix 3 ⊨_
    ⊨_ : Ty → Set
    ⊨ α P   = Syn (α P) × (⊨ᵅ P)
    ⊨ A ▻ B = Syn (A ▻ B) × (⊨ A → ⊨ B)
    ⊨ A ∧ B = ⊨ A × ⊨ B
    ⊨ ⊤    = 𝟙

    infix 3 ⊨⋆_
    ⊨⋆_ : Cx Ty → Set
    ⊨⋆ ⌀     = 𝟙
    ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


  -- Truth in all models.

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
