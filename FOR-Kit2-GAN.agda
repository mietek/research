module FOR-Kit2-GAN where

open import FOR-Kit2 public
open import FOR-GAN public


----------------------------------------------------------------------------------------------------

module RenSubKit1-GAN (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  open RenSubKit1 ¶

  module _ (⚠ : FunExt) where
    ⟪ren⟫ : ∀ (A : Ty) → Presheaf ⟪⊇⟫ lzero
    ⟪ren⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = ren
                ; idƒ  = ⚠ lidren
                ; _∘ƒ_ = λ js′ js → ⚠ (compren js′ js)
                }

    ⟪ren§⟫ : ∀ (Δ : Ctx) → Presheaf ⟪⊇⟫ lzero
    ⟪ren§⟫ Δ = record
                 { ƒObj = _⊢§ Δ
                 ; ƒ    = ren§ -- flip _◐_
                 ; idƒ  = ⚠ lidren§
                 ; _∘ƒ_ = λ js′ js → ⚠ (compren§ js′ js)
                 }

    ⟪get§⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ lzero
    ⟪get§⟫ Γ = record
                 { ƒObj = Γ ⊢§_
                 ; ƒ    = get§ -- _◑_
                 ; idƒ  = ⚠ lidget§
                 ; _∘ƒ_ = λ e e′ → ⚠ (compget§ e e′)
                 }


----------------------------------------------------------------------------------------------------

module RenSubKit2-GAN (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  open RenSubKit2 ¶


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
            ; _∘_  = sub§ -- flip _●_
            ; lid▻ = lidsub§
            ; rid▻ = ridsub§
            ; ass▻ = asssub§
            ; ◅ssa = λ ts ss ss′ → asssub§ ss′ ss ts ⁻¹
            }

  ⟪⊢§⟫ : Category lzero lzero
  ⟪⊢§⟫ = ⟪§⊣⟫ ᵒᵖ

  module _ (⚠ : FunExt) where
    ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪⊢§⟫ lzero
    ⟪sub⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub
                ; idƒ  = ⚠ lidsub
                ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                }


----------------------------------------------------------------------------------------------------
