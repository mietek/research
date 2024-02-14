----------------------------------------------------------------------------------------------------

-- structured properties of first-order renamings

module FOR-GAN {𝓍} {X : Set 𝓍} where

open import FOR public
open import GAN public


----------------------------------------------------------------------------------------------------

⟪⊆⟫ : Category 𝓍 𝓍
⟪⊆⟫ = record
        { Obj  = List X
        ; _▻_  = _⊆_
        ; id   = id⊆
        ; _∘_  = _∘⊆_ -- flip _○_
        ; lid▻ = lid⊆
        ; rid▻ = rid⊆
        ; ass▻ = ass⊆
        ; ◅ssa = λ is″ is′ is → ass⊆ is is′ is″ ⁻¹
        }

⟪⊇⟫ : Category 𝓍 𝓍
⟪⊇⟫ = ⟪⊆⟫ ᵒᵖ

module _ (⚠ : FunExt) where
  ⟪ren∋⟫ : ∀ (A : X) → Presheaf ⟪⊇⟫ lzero
  ⟪ren∋⟫ A = record
               { ƒObj = _∋ A
               ; ƒ    = ren∋
               ; idƒ  = ⚠ idren∋
               ; _∘ƒ_ = λ is′ is → ⚠ (compren∋ is′ is)
               }


----------------------------------------------------------------------------------------------------
