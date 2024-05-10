{-# OPTIONS --allow-unsolved-metas #-}

module A201605.AltArtemov.Old.GN!.True where

open import A201605.AltArtemov.Old.GN!.Core public


data True (Γ : Cx) : ∀ {n} → Ty n → Set where
  var  : ∀ {n} {A : Ty n} → Var Γ A → True Γ A
  lam  : ∀ {n} {A B : Ty n} → True (Γ , A) B → True Γ (A ⊃ B)
  app  : ∀ {n} {A B : Ty n} → True Γ (A ⊃ B) → True Γ A → True Γ B
  pair : ∀ {n} {A B : Ty n} → True Γ A → True Γ B → True Γ (A ∧ B)
  fst  : ∀ {n} {A B : Ty n} → True Γ (A ∧ B) → True Γ A
  snd  : ∀ {n} {A B : Ty n} → True Γ (A ∧ B) → True Γ B
  up   : ∀ {n} {t : Tm 0 n} {A : Ty n} → True Γ (t ∶ A) → True Γ (! t ∶ t ∶ A)
  down : ∀ {n} {t : Tm 0 n} {A : Ty n} → True Γ (t ∶ A) → True Γ A

-- TODO: unfinished
ᵗ⌊_⌋ : ∀ {Γ n} {A : Ty n} → True Γ A → Tm ᵍ⌊ Γ ⌋ n
ᵗ⌊ var x ⌋      = VAR ⁱ⌊ x ⌋
ᵗ⌊ lam j ⌋      = LAM ᵗ⌊ j ⌋
ᵗ⌊ app j₁ j₂ ⌋  = APP ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ pair j₁ j₂ ⌋ = PAIR ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ fst j ⌋      = FST ᵗ⌊ j ⌋
ᵗ⌊ snd j ⌋      = SND ᵗ⌊ j ⌋
ᵗ⌊ up j ⌋       = UP (! ᵗ⌊ j ⌋)
ᵗ⌊ down j ⌋     = DOWN {!ᵗ⌊ j ⌋!}
