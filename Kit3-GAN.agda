module Kit3-GAN where

open import Kit3 public
open import GAN public


----------------------------------------------------------------------------------------------------

module ProgKit-GAN (¶ : ProgKitParams) where
  open ProgKitParams ¶
  open ProgKit ¶

  module _ (⚠ : FunExt) where
    uni¬RF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ RF t) → ¬p ≡ ¬p′
    uni¬RF = uni→ ⚠ uni𝟘

    NF≃¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t ≃ (¬ RF t)
    NF≃¬RF = record
      { to      = NF→¬RF
      ; from    = ¬RF→NF
      ; from∘to = λ p → uniNF ((¬RF→NF ∘ NF→¬RF) p) p
      ; to∘from = λ p → uni¬RF ((NF→¬RF ∘ ¬RF→NF) p) p
      }


----------------------------------------------------------------------------------------------------
