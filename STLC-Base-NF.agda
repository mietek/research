----------------------------------------------------------------------------------------------------

-- β-short normal forms

module STLC-Base-NF where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝ : ∀ {A B} {t : Γ , A ⊢ B} (p : NF t) → NF (⌜λ⌝ t)
    nnf : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : NNF§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} (ψ : NNF§ τ) (p : NNF t) → NNF§ (τ , t)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (⌜λ⌝ p) (⌜λ⌝ p′) = ⌜λ⌝ & uniNF p p′
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-        var-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NF t → NF (ren ϱ t)
  renNF ϱ (⌜λ⌝ p) = ⌜λ⌝ (renNF (lift⊑ ϱ) p)
  renNF ϱ (nnf p) = nnf (renNNF ϱ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF t → NNF (ren ϱ t)
  renNNF ϱ var-        = var-
  renNNF ϱ (p₁ ⌜$⌝ p₂) = renNNF ϱ p₁ ⌜$⌝ renNF ϱ p₂

-- TODO: kit
renNNF§ : ∀ {Γ Γ′ Δ} {σ : Γ ⊢§ Δ} (ϱ : Γ ⊑ Γ′) → NNF§ σ → NNF§ (ren§ ϱ σ)
renNNF§ ϱ ∙       = ∙
renNNF§ ϱ (ψ , p) = renNNF§ ϱ ψ , renNNF ϱ p

wkNNF§ : ∀ {B Γ Δ} {σ : Γ ⊢§ Δ} → NNF§ σ → NNF§ (wk§ {B} σ)
wkNNF§ ψ = renNNF§ (wk⊑ id⊑) ψ

liftNNF§ : ∀ {B Γ Δ} {σ : Γ ⊢§ Δ} → NNF§ σ → NNF§ (lift§ {B} σ)
liftNNF§ ψ = wkNNF§ ψ , var-

sub∋NNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NNF (sub∋ σ i)
sub∋NNF {i = zero}  (ψ , p) = p
sub∋NNF {i = wk∋ i} (ψ , p) = sub∋NNF ψ

mutual
  subNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF t → NF (sub σ t)
  subNF ψ (⌜λ⌝ p) = ⌜λ⌝ (subNF (liftNNF§ ψ) p)
  subNF ψ (nnf p) = nnf (subNNF ψ p)

  subNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF t → NNF (sub σ t)
  subNNF ψ var-        = sub∋NNF ψ
  subNNF ψ (p₁ ⌜$⌝ p₂) = subNNF ψ p₁ ⌜$⌝ subNF ψ p₂


----------------------------------------------------------------------------------------------------
