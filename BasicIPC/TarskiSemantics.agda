module BasicIPC.TarskiSemantics where

open import BasicIPC public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Truth for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public


-- Truth for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 ⊨_
  ⊨_ : Ty → Set
  ⊨ α P   = ⊨ᵅ P
  ⊨ A ▷ B = ⊨ A → ⊨ B
  ⊨ A ∧ B = ⊨ A ᴬᵍ∧ ⊨ B
  ⊨ ⊤    = ᴬᵍ⊤

  infix 3 ⊨⋆_
  ⊨⋆_ : Cx Ty → Set
  ⊨⋆ ⌀     = ᴬᵍ⊤
  ⊨⋆ Γ , A = ⊨⋆ Γ ᴬᵍ∧ ⊨ A


-- Truth in all models.

infix 3 _ᴹ⊨_
_ᴹ⊨_ : Cx Ty → Ty → Set₁
Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A


-- Additional useful equipment.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
lookup top     γ = ᴬᵍsnd γ
lookup (pop i) γ = lookup i (ᴬᵍfst γ)
