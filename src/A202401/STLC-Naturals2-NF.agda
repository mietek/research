----------------------------------------------------------------------------------------------------

-- β-short η-long normal forms, after Abel

module A202401.STLC-Naturals2-NF where

open import A202401.STLC-Naturals2 public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝    : ∀ {A B} {t : Γ , A ⊢ B} (p : NF t) → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF (con ⌜zero⌝)
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (con ⌜suc⌝ ⌜$⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} (pₙ : NNF tₙ)
              (p₀ : NF t₀) (p₁ : NF t₁) →
            NNF (con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ t₁)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (⌜λ⌝ p)           (⌜λ⌝ p′)           = ⌜λ⌝ & uniNF p p′
  uniNF ⌜zero⌝            ⌜zero⌝             = refl
  uniNF (⌜suc⌝ p)         (⌜suc⌝ p′)         = ⌜suc⌝ & uniNF p p′
  uniNF (⌜suc⌝ p)         (nnf (() ⌜$⌝ p₂′))
  uniNF (nnf (() ⌜$⌝ p₂)) (⌜suc⌝ p′)
  uniNF (nnf p)           (nnf p′)           = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-                        var-                         = refl
  uniNNF (p₁ ⌜$⌝ p₂)                 (p₁′ ⌜$⌝ p₂′)                = _⌜$⌝_ & uniNNF p₁ p₁′
                                                                      ⊗ uniNF p₂ p₂′
  uniNNF (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂) (⌜rec⌝ pₙ′ p₀′ pₛ′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (⌜rec⌝ pₙ′ p₀′ pₛ′)          = ⌜rec⌝ & uniNNF pₙ pₙ′
                                                                      ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NF t → NF (ren ϱ t)
  renNF ϱ (⌜λ⌝ p)   = ⌜λ⌝ (renNF (lift⊑ ϱ) p)
  renNF ϱ ⌜zero⌝    = ⌜zero⌝
  renNF ϱ (⌜suc⌝ p) = ⌜suc⌝ (renNF ϱ p)
  renNF ϱ (nnf p)   = nnf (renNNF ϱ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF t → NNF (ren ϱ t)
  renNNF ϱ var-             = var-
  renNNF ϱ (p₁ ⌜$⌝ p₂)      = renNNF ϱ p₁ ⌜$⌝ renNF ϱ p₂
  renNNF ϱ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF ϱ pₙ) (renNF ϱ p₀) (renNF ϱ pₛ)


----------------------------------------------------------------------------------------------------

mutual
  infix 3 _⊢≪_
  data _⊢≪_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝    : ∀ {A B} (t : Γ , A ⊢≪ B) → Γ ⊢≪ A ⌜⊃⌝ B
    ⌜zero⌝ : Γ ⊢≪ ⌜ℕ⌝
    ⌜suc⌝  : ∀ (t : Γ ⊢≪ ⌜ℕ⌝) → Γ ⊢≪ ⌜ℕ⌝
    nnf    : ∀ (t : Γ ⊢≫ ⌜ℕ⌝) → Γ ⊢≪ ⌜ℕ⌝

  infix 3 _⊢≫_
  data _⊢≫_ (Γ : Ctx) : Ty → Set where
    var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢≫ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢≫ A ⌜⊃⌝ B) (t₂ : Γ ⊢≪ A) → Γ ⊢≫ B
    ⌜rec⌝ : ∀ {A} (tₙ : Γ ⊢≫ ⌜ℕ⌝) (t₀ : Γ ⊢≪ A) (tₛ : Γ ⊢≪ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) → Γ ⊢≫ A


----------------------------------------------------------------------------------------------------

mutual
  ren≪ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢≪ A → Γ′ ⊢≪ A
  ren≪ ϱ (⌜λ⌝ t)   = ⌜λ⌝ (ren≪ (lift⊑ ϱ) t)
  ren≪ ϱ ⌜zero⌝    = ⌜zero⌝
  ren≪ ϱ (⌜suc⌝ t) = ren≪ ϱ t
  ren≪ ϱ (nnf t)   = nnf (ren≫ ϱ t)

  ren≫ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢≫ A → Γ′ ⊢≫ A
  ren≫ ϱ (var i)          = var (ren∋ ϱ i)
  ren≫ ϱ (t₁ ⌜$⌝ t₂)      = ren≫ ϱ t₁ ⌜$⌝ ren≪ ϱ t₂
  ren≫ ϱ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren≫ ϱ tₙ) (ren≪ ϱ t₀) (ren≪ ϱ tₛ)


----------------------------------------------------------------------------------------------------
