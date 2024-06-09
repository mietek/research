module A202401.Kit2-GAN where

open import A202401.Kit2 public
open import A202401.OPE-GAN public


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

    ϖren∘lift⊑ : Ty → Ty → Presheaf ⟪⊒⟫ lzero
    ϖren∘lift⊑ A B = record
                       { ƒObj = λ Γ → Γ , B ⊢ A
                       ; ƒ    = ren ∘ lift⊑
                       ; idƒ  = ⚠ lidren
                       ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren (lift⊑ ϱ′) (lift⊑ ϱ))
                       }

    νwk : ∀ (A B : Ty) → NatTrans (ϖren A) (ϖren∘lift⊑ A B)
    νwk A B = record
                { ν    = λ Γ → wk
                ; natν = λ Γ Γ′ ϱ → ⚠ λ t → eqwkren ϱ t ⁻¹
                }

    ϖren§∘lift⊑ : Ctx → Ty → Presheaf ⟪⊒⟫ lzero
    ϖren§∘lift⊑ Δ B = record
                        { ƒObj = λ Γ → Γ , B ⊢§ Δ
                        ; ƒ    = ren§ ∘ lift⊑
                        ; idƒ  = ⚠ lidren§
                        ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren§ (lift⊑ ϱ′) (lift⊑ ϱ))
                        }

    νwk§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (ϖren§ Δ) (ϖren§∘lift⊑ Δ B)
    νwk§ Δ B = record
                 { ν    = λ Γ → wk§
                 ; natν = λ Γ Γ′ ϱ → ⚠ λ ts → eqwkren§ ϱ ts ⁻¹
                 }

    ϖren§∘lift⊑′ : Ctx → Ty → Presheaf ⟪⊒⟫ lzero
    ϖren§∘lift⊑′ Δ B = record
                         { ƒObj = λ Γ → Γ , B ⊢§ Δ , B
                         ; ƒ    = ren§ ∘ lift⊑
                         ; idƒ  = ⚠ lidren§
                         ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren§ (lift⊑ ϱ′) (lift⊑ ϱ))
                         }

    νlift§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (ϖren§ Δ) (ϖren§∘lift⊑′ Δ B)
    νlift§ Δ B = record
                   { ν    = λ Γ → lift§
                   ; natν = λ Γ Δ ϱ → ⚠ λ ts → eqliftren§ ϱ ts ⁻¹
                   }

    ϖget§ : Ctx → Presheaf ⟪⊑⟫ lzero
    ϖget§ Γ = record
                { ƒObj = Γ ⊢§_
                ; ƒ    = get§
                ; idƒ  = ⚠ lidget§
                ; _∘ƒ_ = λ ϱ ϱ′ → ⚠ (compget§ ϱ ϱ′)
                }

    νren§ : ∀ (Γ Γ′ : Ctx) → Γ ⊑ Γ′ → NatTrans (ϖget§ Γ) (ϖget§ Γ′)
    νren§ Γ Γ′ ϱ = record
                     { ν    = λ Δ → ren§ ϱ
                     ; natν = λ Γ Δ ϱ′ → ⚠ λ ts → eqrenget§ ϱ ϱ′ ts ⁻¹
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
    ϖsub : Ty → Presheaf ⟪⊢§⟫ lzero
    ϖsub A = record
               { ƒObj = _⊢ A
               ; ƒ    = sub
               ; idƒ  = ⚠ lidsub
               ; _∘ƒ_ = λ σ′ σ → ⚠ (compsub σ′ σ)
               }


----------------------------------------------------------------------------------------------------
