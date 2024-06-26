----------------------------------------------------------------------------------------------------

-- properties of first-order renamings

module A202401.FOR-GAN {𝓍} {X : Set 𝓍} where

open import A202401.FOR public
open import A202401.GAN public


----------------------------------------------------------------------------------------------------

⟪⊑⟫ : Category 𝓍 𝓍
⟪⊑⟫ = record
        { Obj  = Rist X
        ; _▻_  = _⊑_
        ; id   = id⊑
        ; _∘_  = _∘⊑_
        ; lid▻ = lid⊑
        ; rid▻ = rid⊑
        ; ass▻ = ass⊑
        ; ◅ssa = λ ϱ″ ϱ′ ϱ → ass⊑ ϱ ϱ′ ϱ″ ⁻¹
        }

⟪⊒⟫ : Category 𝓍 𝓍
⟪⊒⟫ = ⟪⊑⟫ ᵒᵖ

module _ (⚠ : FunExt) where
  ϖren∋ : X → Presheaf ⟪⊒⟫ 𝓍
  ϖren∋ A = record
              { ƒObj = _∋ A
              ; ƒ    = ren∋
              ; idƒ  = ⚠ idren∋
              ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren∋ ϱ′ ϱ)
              }


----------------------------------------------------------------------------------------------------
