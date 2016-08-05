module BasicIPC.Hilbert.ContextFree.Nested.TarskiBasicCompleteness where

open import BasicIPC.Hilbert.ContextFree.Nested.TarskiSoundness.CoquandDybjer public


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⊢ α P
    }


-- Completeness, or quotation.

quot : ∀ {A} → ᴹ⊨ A → ⊢ A
quot t = reify t


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval


-- Correctness of normalisation with respect to conversion.

module _ {{_ : Model}} where
  check′ : ∀ {A} {t t′ : ⊢ A} → t ⇒ t′ → norm t ≡ norm t′
  check′ p = cong reify (check p)
