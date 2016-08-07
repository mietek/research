module BasicIS4.Hilbert.Tree.TarskiBasicCompleteness where

open import BasicIS4.Hilbert.Tree.TarskiSoundness public




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
  quot t = reify t


  -- Normalisation by evaluation.

  norm : ∀ {A} → ⊢ A → ⊢ A
  norm = quot ∘ eval


  -- Correctness of normalisation with respect to conversion.

  check′ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → norm t ≡ norm t′
  check′ p = cong reify (check p)
