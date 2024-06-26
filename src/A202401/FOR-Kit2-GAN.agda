module A202401.FOR-Kit2-GAN where

open import A202401.FOR-Kit2 public
open import A202401.FOR-GAN public


----------------------------------------------------------------------------------------------------

module RenSubKit1-GAN (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  open RenSubKit1 ¶

  module _ (⚠ : FunExt) where
    ϖren : Ty → Presheaf ⟪⊒⟫ lzero
    ϖren A = record
               { ƒObj = _⊢ A
               ; ƒ    = ren
               ; idƒ  = ⚠ lidren
               ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren ϱ′ ϱ)
               }

    ϖren§ : Ctx → Presheaf ⟪⊒⟫ lzero
    ϖren§ Δ = record
                { ƒObj = _⊢§ Δ
                ; ƒ    = ren§
                ; idƒ  = ⚠ lidren§
                ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren§ ϱ′ ϱ)
                }

    ϖget§ : Ctx → Presheaf ⟪⊑⟫ lzero
    ϖget§ Γ = record
                { ƒObj = Γ ⊢§_
                ; ƒ    = get§
                ; idƒ  = ⚠ lidget§
                ; _∘ƒ_ = λ e e′ → ⚠ (compget§ e e′)
                }


----------------------------------------------------------------------------------------------------

module RenSubKit2-GAN (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  open RenSubKit2 ¶

  -- TODO: more GAN


----------------------------------------------------------------------------------------------------

module RenSubKit3-GAN (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  open RenSubKit3 ¶


----------------------------------------------------------------------------------------------------

module RenSubKit4-GAN (¶ : RenSubKit4Params) where
  open RenSubKit4Params ¶
  open RenSubKit4 ¶

  ⟪§⊣⟫ : Category lzero lzero
  ⟪§⊣⟫ = record
            { Obj  = Ctx
            ; _▻_  = flip _⊢§_
            ; id   = id§
            ; _∘_  = sub§
            ; lid▻ = lidsub§
            ; rid▻ = ridsub§
            ; ass▻ = asssub§
            ; ◅ssa = λ τ σ σ′ → asssub§ σ′ σ τ ⁻¹
            }

  ⟪⊢§⟫ : Category lzero lzero
  ⟪⊢§⟫ = ⟪§⊣⟫ ᵒᵖ

  module _ (⚠ : FunExt) where
    ⟪sub⟫ : Ty → Presheaf ⟪⊢§⟫ lzero
    ⟪sub⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub
                ; idƒ  = ⚠ lidsub
                ; _∘ƒ_ = λ σ′ σ → ⚠ (compsub σ′ σ)
                }


----------------------------------------------------------------------------------------------------
