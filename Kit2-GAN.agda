module Kit2-GAN where

open import Kit2 public
open import OPE-GAN public


----------------------------------------------------------------------------------------------------

module RenSubKit1-GAN (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  open RenSubKit1 ¶

  module _ (⚠ : FunExt) where
    pshren : ∀ (A : Ty) → Presheaf ⟪⊇⟫ lzero
    pshren A = record
                 { ƒObj = _⊢ A
                 ; ƒ    = ren
                 ; idƒ  = ⚠ lidren
                 ; _∘ƒ_ = λ e′ e → ⚠ (compren e′ e)
                 }

    pshren§ : ∀ (Δ : Ctx) → Presheaf ⟪⊇⟫ lzero
    pshren§ Δ = record
                  { ƒObj = _⊢§ Δ
                  ; ƒ    = ren§ -- flip _◐_
                  ; idƒ  = ⚠ lidren§
                  ; _∘ƒ_ = λ e′ e → ⚠ (compren§ e′ e)
                  }

    pshren∘lift⊆ : ∀ (A B : Ty) → Presheaf ⟪⊇⟫ lzero
    pshren∘lift⊆ A B = record
                         { ƒObj = λ Γ → B ∷ Γ ⊢ A
                         ; ƒ    = ren ∘ lift⊆
                         ; idƒ  = ⚠ lidren
                         ; _∘ƒ_ = λ e′ e → ⚠ (compren (lift⊆ e′) (lift⊆ e))
                         }

    ntwk : ∀ (A B : Ty) → NatTrans (pshren A) (pshren∘lift⊆ A B)
    ntwk A B = record
                 { η    = λ Γ → wk
                 ; natη = λ Γ Γ′ e → ⚠ λ t → eqwkren e t ⁻¹
                 }

    pshren§∘lift⊆ : ∀ (Δ : Ctx) (B : Ty) → Presheaf ⟪⊇⟫ lzero
    pshren§∘lift⊆ Δ B = record
                          { ƒObj = λ Γ → B ∷ Γ ⊢§ Δ
                          ; ƒ    = ren§ ∘ lift⊆
                          ; idƒ  = ⚠ lidren§
                          ; _∘ƒ_ = λ e′ e → ⚠ (compren§ (lift⊆ e′) (lift⊆ e))
                          }

    ntwk§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (pshren§ Δ) (pshren§∘lift⊆ Δ B)
    ntwk§ Δ B = record
                  { η    = λ Γ → wk§
                  ; natη = λ Γ Γ′ e → ⚠ λ ts → eqwkren§ e ts ⁻¹
                  }

    -- TODO: name?
    pshren§∘lift⊆′ : ∀ (Δ : Ctx) (B : Ty) → Presheaf ⟪⊇⟫ lzero
    pshren§∘lift⊆′ Δ B = record
                           { ƒObj = λ Γ → B ∷ Γ ⊢§ B ∷ Δ
                           ; ƒ    = ren§ ∘ lift⊆
                           ; idƒ  = ⚠ lidren§
                           ; _∘ƒ_ = λ e′ e → ⚠ (compren§ (lift⊆ e′) (lift⊆ e))
                           }

    ntlift§ : ∀ (Δ : Ctx) (B : Ty) → NatTrans (pshren§ Δ) (pshren§∘lift⊆′ Δ B)
    ntlift§ Δ B = record
                    { η    = λ Γ → lift§
                    ; natη = λ Γ Δ e → ⚠ λ ts → eqliftren§ e ts ⁻¹
                    }

    pshget§ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ lzero
    pshget§ Γ = record
                  { ƒObj = Γ ⊢§_
                  ; ƒ    = get§ -- _◑_
                  ; idƒ  = ⚠ lidget§
                  ; _∘ƒ_ = λ e e′ → ⚠ (compget§ e e′)
                  }

    ntren§ : ∀ (Γ Γ′ : Ctx) (e : Γ ⊆ Γ′) → NatTrans (pshget§ Γ) (pshget§ Γ′)
    ntren§ Γ Γ′ e = record
                      { η    = λ Δ → ren§ e
                      ; natη = λ Γ Δ e′ → ⚠ λ ts → eqrenget§ e e′ ts ⁻¹
                      }


----------------------------------------------------------------------------------------------------

module RenSubKit2-GAN (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  open RenSubKit2 ¶


----------------------------------------------------------------------------------------------------

module RenSubKit3-GAN (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  open RenSubKit3 ¶

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
    pshsub : ∀ (A : Ty) → Presheaf ⟪⊢§⟫ lzero
    pshsub A = record
                 { ƒObj = _⊢ A
                 ; ƒ    = sub
                 ; idƒ  = ⚠ lidsub
                 ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                 }


----------------------------------------------------------------------------------------------------
