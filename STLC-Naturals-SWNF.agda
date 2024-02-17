----------------------------------------------------------------------------------------------------

-- β-short semi-weak normal forms

module STLC-Naturals-SWNF where

open import STLC-Naturals public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : Γ , A ⊢ B} → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF ⌜zero⌝
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜suc⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : (Γ , ⌜ℕ⌝) , A ⊢ A} (pₙ : NNF tₙ)
              (p₀ : NF t₀) (p₁ : NF t₁) →
            NNF (⌜rec⌝ tₙ t₀ t₁)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : NNF§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} → NNF§ τ → NNF t → NNF§ (τ , t)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-      ⌜λ⌝-       = refl
  uniNF ⌜zero⌝    ⌜zero⌝     = refl
  uniNF (⌜suc⌝ p) (⌜suc⌝ p′) = ⌜suc⌝ & uniNF p p′
  uniNF (nnf p)   (nnf p′)   = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-             var-                = refl
  uniNNF (p₁ ⌜$⌝ p₂)      (p₁′ ⌜$⌝ p₂′)       = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜rec⌝ pₙ p₀ pₛ) (⌜rec⌝ pₙ′ p₀′ pₛ′) = ⌜rec⌝ & uniNNF pₙ pₙ′ ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NF t → NF (ren ρ t)
  renNF ρ ⌜λ⌝-      = ⌜λ⌝-
  renNF ρ ⌜zero⌝    = ⌜zero⌝
  renNF ρ (⌜suc⌝ p) = ⌜suc⌝ (renNF ρ p)
  renNF ρ (nnf p)   = nnf (renNNF ρ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NNF t → NNF (ren ρ t)
  renNNF ρ var-             = var-
  renNNF ρ (p₁ ⌜$⌝ p₂)      = renNNF ρ p₁ ⌜$⌝ renNF ρ p₂
  renNNF ρ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF ρ pₙ) (renNF ρ p₀) (renNF (lift⊑ (lift⊑ ρ)) pₛ)

-- TODO: kit
renNNF§ : ∀ {Γ Γ′ Δ} {τ : Γ ⊢§ Δ} (ρ : Γ ⊑ Γ′) → NNF§ τ → NNF§ (ren§ ρ τ)
renNNF§ ρ ∙       = ∙
renNNF§ ρ (ψ , p) = renNNF§ ρ ψ , renNNF ρ p

wkNNF§ : ∀ {B Γ Δ} {τ : Γ ⊢§ Δ} → NNF§ τ → NNF§ (wk§ {B} τ)
wkNNF§ ψ = renNNF§ (wk⊑ id⊑) ψ

liftNNF§ : ∀ {B Γ Δ} {τ : Γ ⊢§ Δ} → NNF§ τ → NNF§ (lift§ {B} τ)
liftNNF§ ψ = wkNNF§ ψ , var-

sub∋NNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NNF (sub∋ σ i)
sub∋NNF {i = zero}  (ψ , p) = p
sub∋NNF {i = wk∋ i} (ψ , p) = sub∋NNF ψ

mutual
  subNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF t → NF (sub σ t)
  subNF ψ ⌜λ⌝-      = ⌜λ⌝-
  subNF ψ ⌜zero⌝    = ⌜zero⌝
  subNF ψ (⌜suc⌝ p) = ⌜suc⌝ (subNF ψ p)
  subNF ψ (nnf p)   = nnf (subNNF ψ p)

  subNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF t → NNF (sub σ t)
  subNNF ψ var-             = sub∋NNF ψ
  subNNF ψ (p₁ ⌜$⌝ p₂)      = subNNF ψ p₁ ⌜$⌝ subNF ψ p₂
  subNNF ψ (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (subNNF ψ pₙ) (subNF ψ p₀)
                                 (subNF (liftNNF§ (liftNNF§ ψ)) pₛ)


----------------------------------------------------------------------------------------------------
