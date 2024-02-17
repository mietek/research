----------------------------------------------------------------------------------------------------

-- β-short weak normal forms

module STLC-Negative-WNF where

open import STLC-Negative public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : Γ , A ⊢ B} → NF (⌜λ⌝ t)
    -⌜,⌝-  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → NF (t₁ ⌜,⌝ t₂)
    ⌜unit⌝ : NF ⌜unit⌝
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜fst⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜fst⌝ t)
    ⌜snd⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜snd⌝ t)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : NNF§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} → NNF§ τ → NNF t → NNF§ (τ , t)

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

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NF t → NF (ren ρ t)
  renNF ρ ⌜λ⌝-    = ⌜λ⌝-
  renNF ρ -⌜,⌝-   = -⌜,⌝-
  renNF ρ ⌜unit⌝  = ⌜unit⌝
  renNF ρ (nnf p) = nnf (renNNF ρ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → NNF t → NNF (ren ρ t)
  renNNF ρ var-        = var-
  renNNF ρ (p₁ ⌜$⌝ p₂) = renNNF ρ p₁ ⌜$⌝ renNF ρ p₂
  renNNF ρ (⌜fst⌝ p)   = ⌜fst⌝ (renNNF ρ p)
  renNNF ρ (⌜snd⌝ p)   = ⌜snd⌝ (renNNF ρ p)

sub∋NNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NNF (sub∋ σ i)
sub∋NNF {i = zero}  (ψ , p) = p
sub∋NNF {i = wk∋ i} (ψ , p) = sub∋NNF ψ

mutual
  subNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF t → NF (sub σ t)
  subNF ψ ⌜λ⌝-    = ⌜λ⌝-
  subNF ψ -⌜,⌝-   = -⌜,⌝-
  subNF ψ ⌜unit⌝  = ⌜unit⌝
  subNF ψ (nnf p) = nnf (subNNF ψ p)

  subNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF t → NNF (sub σ t)
  subNNF ψ var-        = sub∋NNF ψ
  subNNF ψ (p₁ ⌜$⌝ p₂) = subNNF ψ p₁ ⌜$⌝ subNF ψ p₂
  subNNF ψ (⌜fst⌝ p)   = ⌜fst⌝ (subNNF ψ p)
  subNNF ψ (⌜snd⌝ p)   = ⌜snd⌝ (subNNF ψ p)


----------------------------------------------------------------------------------------------------
