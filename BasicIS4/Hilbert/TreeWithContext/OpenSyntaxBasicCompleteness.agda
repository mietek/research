module BasicIS4.Hilbert.TreeWithContext.OpenSyntaxBasicCompleteness where

open import BasicIS4.Hilbert.TreeWithContext.OpenSyntaxSoundness public




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerBasicCompleteness where
  open CoquandDybjerSoundness


  -- The canonical model.

  instance
    canon : Model
    canon = record
      { ⊨ᵅ_ = λ P → ⌀ ⊢ α P
      }


  -- Completeness with respect to all models, or quotation.

  -- FIXME: What is wrong here?
  postulate
    quot : ∀ {A Γ} → Γ ᴹ⊨ A → Γ ⊢ A


  -- Normalisation by evaluation.

  norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
  norm = quot ∘ eval
