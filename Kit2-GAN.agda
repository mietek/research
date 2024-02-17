module Kit2-GAN where

open import Kit2 public
open import OPE-GAN public


----------------------------------------------------------------------------------------------------

module RenSubKit1-GAN (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  open RenSubKit1 ¶

  module _ (⚠ : FunExt) where
    ψren : Ty → Presheaf ⟪⊒⟫ lzero
    ψren A = record
               { ƒObj = _⊢ A
               ; ƒ    = ren
               ; idƒ  = ⚠ lidren
               ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren ρ′ ρ)
               }

    ψren§ : Ctx → Presheaf ⟪⊒⟫ lzero
    ψren§ Δ = record
                { ƒObj = _⊢§ Δ
                ; ƒ    = ren§
                ; idƒ  = ⚠ lidren§
                ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren§ ρ′ ρ)
                }

    ψren∘lift⊑ : Ty → Ty → Presheaf ⟪⊒⟫ lzero
    ψren∘lift⊑ A B = record
                       { ƒObj = λ Γ → Γ , B ⊢ A
                       ; ƒ    = ren ∘ lift⊑
                       ; idƒ  = ⚠ lidren
                       ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren (lift⊑ ρ′) (lift⊑ ρ))
                       }

    ηwk : ∀ (A B : Ty) → NatTrans (ψren A) (ψren∘lift⊑ A B)
    ηwk A B = record
                { η    = λ Γ → wk
                ; natη = λ Γ Γ′ ρ → ⚠ λ t → eqwkren ρ t ⁻¹
                }

    ψren§∘lift⊑ : Ctx → Ty → Presheaf ⟪⊒⟫ lzero
    ψren§∘lift⊑ Δ B = record
                        { ƒObj = λ Γ → Γ , B ⊢§ Δ
                        ; ƒ    = ren§ ∘ lift⊑
                        ; idƒ  = ⚠ lidren§
                        ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren§ (lift⊑ ρ′) (lift⊑ ρ))
                        }

    ηwk§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (ψren§ Δ) (ψren§∘lift⊑ Δ B)
    ηwk§ Δ B = record
                 { η    = λ Γ → wk§
                 ; natη = λ Γ Γ′ ρ → ⚠ λ ts → eqwkren§ ρ ts ⁻¹
                 }

    ψren§∘lift⊑′ : Ctx → Ty → Presheaf ⟪⊒⟫ lzero
    ψren§∘lift⊑′ Δ B = record
                         { ƒObj = λ Γ → Γ , B ⊢§ Δ , B
                         ; ƒ    = ren§ ∘ lift⊑
                         ; idƒ  = ⚠ lidren§
                         ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren§ (lift⊑ ρ′) (lift⊑ ρ))
                         }

    ηlift§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (ψren§ Δ) (ψren§∘lift⊑′ Δ B)
    ηlift§ Δ B = record
                   { η    = λ Γ → lift§
                   ; natη = λ Γ Δ ρ → ⚠ λ ts → eqliftren§ ρ ts ⁻¹
                   }

    ψget§ : Ctx → Presheaf ⟪⊑⟫ lzero
    ψget§ Γ = record
                { ƒObj = Γ ⊢§_
                ; ƒ    = get§
                ; idƒ  = ⚠ lidget§
                ; _∘ƒ_ = λ ρ ρ′ → ⚠ (compget§ ρ ρ′)
                }

    ηren§ : ∀ (Γ Γ′ : Ctx) → Γ ⊑ Γ′ → NatTrans (ψget§ Γ) (ψget§ Γ′)
    ηren§ Γ Γ′ ρ = record
                     { η    = λ Δ → ren§ ρ
                     ; natη = λ Γ Δ ρ′ → ⚠ λ ts → eqrenget§ ρ ρ′ ts ⁻¹
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
    ψsub : Ty → Presheaf ⟪⊢§⟫ lzero
    ψsub A = record
               { ƒObj = _⊢ A
               ; ƒ    = sub
               ; idƒ  = ⚠ lidsub
               ; _∘ƒ_ = λ σ′ σ → ⚠ (compsub σ′ σ)
               }


----------------------------------------------------------------------------------------------------
