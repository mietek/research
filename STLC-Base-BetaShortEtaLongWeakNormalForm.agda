module STLC-Base-BetaShortEtaLongWeakNormalForm where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  data FNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → FNF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : FNNF t) → FNF t

  data FNNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → FNNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : FNNF t₁) (p₂ : FNF t₂) →
            FNNF (t₁ ⌜$⌝ t₂)

data FNNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : FNNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → FNNF t → FNNF* ts → FNNF* (t ∷ ts)

mutual
  uniFNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNF t) → p ≡ p′
  uniFNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniFNF (nnf p) (nnf p′) = nnf & uniFNNF p p′

  uniFNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNNF t) → p ≡ p′
  uniFNNF var-        var-          = refl
  uniFNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

mutual
  FNF? : ∀ {A Γ} (t : Γ ⊢ A) → Dec (FNF t)
  FNF? {⌜◦⌝}     (var i)     = yes (nnf var-)
  FNF? {⌜◦⌝}     (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂        = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂        = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _             = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
  FNF? {A ⌜⊃⌝ B} (var i)     = no λ ()
  FNF? {A ⌜⊃⌝ B} (⌜λ⌝ t)     = yes ⌜λ⌝-
  FNF? {A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) = no λ ()

  FNNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNNF t)
  FNNF? (var i)         = yes var-
  FNNF? (⌜λ⌝ t)         = no λ ()
  FNNF? (t₁ ⌜$⌝ t₂)     with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------
