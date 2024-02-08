module STLC-Negative-BetaShortWeakNormalForm where

open import STLC-Negative public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    -⌜,⌝-  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → NF (t₁ ⌜,⌝ t₂)
    ⌜unit⌝ : NF ⌜unit⌝
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜fst⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜fst⌝ t)
    ⌜snd⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜snd⌝ t)

data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : NNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniNF -⌜,⌝-   -⌜,⌝-    = refl
  uniNF ⌜unit⌝  ⌜unit⌝   = refl
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NNF d) → p ≡ p′
  uniNNF var-        var-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜fst⌝ p)   (⌜fst⌝ p′)    = ⌜fst⌝ & uniNNF p p′
  uniNNF (⌜snd⌝ p)   (⌜snd⌝ p′)    = ⌜snd⌝ & uniNNF p p′


----------------------------------------------------------------------------------------------------
