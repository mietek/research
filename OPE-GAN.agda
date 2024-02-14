----------------------------------------------------------------------------------------------------

-- structured properties of order-preserving embeddings

module OPE-GAN {𝓍} {X : Set 𝓍} where

open import OPE public
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
        ; ◅ssa = λ e e′ e″ → ass⊆ e″ e′ e ⁻¹
        }

⟪⊇⟫ : Category 𝓍 𝓍
⟪⊇⟫ = ⟪⊆⟫ ᵒᵖ

⟪lift⊆⟫ : ∀ (B : X) → Functor ⟪⊆⟫ ⟪⊆⟫
⟪lift⊆⟫ B = record
              { ƒObj = B ∷_
              ; ƒ    = lift⊆
              ; idƒ  = refl
              ; _∘ƒ_ = λ e′ e → refl
              }

⟪wk⊆⟫ : ∀ (B : X) → NatTrans (⟪Id⟫ ⟪⊆⟫) (⟪lift⊆⟫ B)
⟪wk⊆⟫ B = record
            { η    = λ Γ → wk⊆ id⊆
            ; natη = λ Γ Δ e → wk⊆ & (lid⊆ e ⋮ rid⊆ e ⁻¹)
            }

module _ (⚠ : FunExt) where
  ⟪ren∋⟫ : ∀ (A : X) → Presheaf ⟪⊇⟫ lzero
  ⟪ren∋⟫ A = record
               { ƒObj = _∋ A
               ; ƒ    = ren∋
               ; idƒ  = ⚠ idren∋
               ; _∘ƒ_ = λ e′ e → ⚠ (compren∋ e′ e)
               }


----------------------------------------------------------------------------------------------------
