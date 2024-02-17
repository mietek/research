----------------------------------------------------------------------------------------------------

-- β-short η-long normal forms, after Abel

module STLC-Naturals2-NF where

open import STLC-Naturals2 public


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

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : NNF§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} → NNF§ τ → NNF t → NNF§ (τ , t)

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
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NF t → NF (ren ρ t)
  renNF ρ (⌜λ⌝ p)   = ⌜λ⌝ (renNF (lift⊑ ρ) p)
  renNF ρ ⌜zero⌝    = ⌜zero⌝
  renNF ρ (⌜suc⌝ p) = ⌜suc⌝ (renNF ρ p)
  renNF ρ (nnf p)   = nnf (renNNF ρ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NNF t → NNF (ren ρ t)
  renNNF ρ var-             = var-
  renNNF ρ (p₁ ⌜$⌝ p₂)      = renNNF ρ p₁ ⌜$⌝ renNF ρ p₂
  renNNF ρ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF ρ pₙ) (renNF ρ p₀) (renNF ρ pₛ)


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
  ren≪ ρ (⌜λ⌝ t)   = ⌜λ⌝ (ren≪ (lift⊑ ρ) t)
  ren≪ ρ ⌜zero⌝    = ⌜zero⌝
  ren≪ ρ (⌜suc⌝ t) = ren≪ ρ t
  ren≪ ρ (nnf t)   = nnf (ren≫ ρ t)

  ren≫ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢≫ A → Γ′ ⊢≫ A
  ren≫ ρ (var i)          = var (ren∋ ρ i)
  ren≫ ρ (t₁ ⌜$⌝ t₂)      = ren≫ ρ t₁ ⌜$⌝ ren≪ ρ t₂
  ren≫ ρ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren≫ ρ tₙ) (ren≪ ρ t₀) (ren≪ ρ tₛ)


----------------------------------------------------------------------------------------------------
