----------------------------------------------------------------------------------------------------

-- β-short weak normal forms

module A202401.STLC-Naturals-WNF where

open import A202401.STLC-Naturals public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : Γ , A ⊢ B} → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF ⌜zero⌝
    ⌜suc⌝- : ∀ {t : Γ ⊢ ⌜ℕ⌝} → NF (⌜suc⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : (Γ , ⌜ℕ⌝) , A ⊢ A} (pₙ : NNF tₙ)
              (p₀ : NF t₀) (p₁ : NF t₁) →
            NNF (⌜rec⌝ tₙ t₀ t₁)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-      ⌜λ⌝-       = refl
  uniNF ⌜zero⌝    ⌜zero⌝     = refl
  uniNF ⌜suc⌝-    ⌜suc⌝-     = refl
  uniNF (nnf p)   (nnf p′)   = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-             var-                = refl
  uniNNF (p₁ ⌜$⌝ p₂)      (p₁′ ⌜$⌝ p₂′)       = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜rec⌝ pₙ p₀ pₛ) (⌜rec⌝ pₙ′ p₀′ pₛ′) = ⌜rec⌝ & uniNNF pₙ pₙ′ ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NF t → NF (ren ϱ t)
  renNF ϱ ⌜λ⌝-      = ⌜λ⌝-
  renNF ϱ ⌜zero⌝    = ⌜zero⌝
  renNF ϱ ⌜suc⌝-    = ⌜suc⌝-
  renNF ϱ (nnf p)   = nnf (renNNF ϱ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF t → NNF (ren ϱ t)
  renNNF ϱ var-             = var-
  renNNF ϱ (p₁ ⌜$⌝ p₂)      = renNNF ϱ p₁ ⌜$⌝ renNF ϱ p₂
  renNNF ϱ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF ϱ pₙ) (renNF ϱ p₀) (renNF (lift⊑ (lift⊑ ϱ)) pₛ)

open RenNNFKit (kit renkit var- (λ {_} {_} {_} {t} → renNNF {t = t})) public

mutual
  subNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF t → NF (sub σ t)
  subNF ψ ⌜λ⌝-      = ⌜λ⌝-
  subNF ψ ⌜zero⌝    = ⌜zero⌝
  subNF ψ ⌜suc⌝-    = ⌜suc⌝-
  subNF ψ (nnf p)   = nnf (subNNF ψ p)

  subNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF t → NNF (sub σ t)
  subNNF ψ var-             = sub∋NNF ψ
  subNNF ψ (p₁ ⌜$⌝ p₂)      = subNNF ψ p₁ ⌜$⌝ subNF ψ p₂
  subNNF ψ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (subNNF ψ pₙ) (subNF ψ p₀)
                                (subNF (liftNNF§ (liftNNF§ ψ)) pₛ)


----------------------------------------------------------------------------------------------------
