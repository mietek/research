module BasicIS4.Hilbert.TreeWithContextPair.OpenSyntaxBasicCompleteness where

open import BasicIS4.Hilbert.TreeWithContextPair.OpenSyntaxSoundness public




-- Using truth with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerBasicCompleteness where
  open CoquandDybjerSoundness


  -- The canonical model.

  instance
    canon : Model
    canon = record
      { ⊨ᵅ_ = λ P → ⌀ ⁏ ⌀ ⊢ α P
      }


  -- Completeness with respect to all models, or quotation.

  -- FIXME: What is wrong here?
  postulate
    quot : ∀ {A Γ Δ} → Γ ⁏ Δ ᴹ⊨ A → Γ ⁏ Δ ⊢ A


  -- Normalisation by evaluation.

  norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
  norm = quot ∘ eval
