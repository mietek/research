module IPC.Hilbert.Tree.TarskiBasicCompleteness where

open import IPC.Hilbert.Tree.TarskiSoundness public




module CoquandDybjerBasicCompleteness where
  open CoquandDybjerSoundness public


  -- The canonical model.

  private
    instance
      canon : Model
      canon = record
        { ⊩ᵅ_ = λ P → ⊢ α P
        }


  -- Completeness with respect to all models, or quotation.

  quot : ∀ {A} → ᴹ⊩ A → ⊢ A
  quot s = reify s


  -- Normalisation by evaluation.

  norm : ∀ {A} → ⊢ A → ⊢ A
  norm = quot ∘ eval


  -- Correctness of normalisation with respect to conversion.

  check′ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm t ≡ norm t′
  check′ p = cong reify (check p)
