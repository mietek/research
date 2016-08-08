module BasicIS4.Hilbert.Tree.OpenSyntaxBasicCompleteness where

open import BasicIS4.Hilbert.Tree.OpenSyntaxSoundness public




-- Using truth with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerBasicCompleteness where
  open CoquandDybjerSoundness


  -- The canonical model.

  instance
    canon : Model
    canon = record
      { ⊨ᵅ_ = λ P → ⊢ α P
      }


  -- Completeness with respect to all models, or quotation.

  quot : ∀ {A} → ᴹ⊨ A → ⊢ A
  quot {A} t = reify {A} t


  -- Normalisation by evaluation.

  norm : ∀ {A} → ⊢ A → ⊢ A
  norm = quot ∘ eval
