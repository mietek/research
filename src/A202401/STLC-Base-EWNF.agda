----------------------------------------------------------------------------------------------------

-- β-short η-long expanded weak normal forms

module A202401.STLC-Base-EWNF where

open import A202401.STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : Γ , A ⊢ B} → NF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) →
            NNF (t₁ ⌜$⌝ t₂)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : NNF§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} (ψ : NNF§ τ) (p : NNF t) → NNF§ (τ , t)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-        var-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′

mutual
  NF? : ∀ {A Γ} (t : Γ ⊢ A) → Dec (NF t)
  NF? {⌜◦⌝}     (var i)     = yes (nnf var-)
  NF? {⌜◦⌝}     (t₁ ⌜$⌝ t₂) with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂       = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂       = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _            = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
  NF? {A ⌜⊃⌝ B} (var i)     = no λ ()
  NF? {A ⌜⊃⌝ B} (⌜λ⌝ t)     = yes ⌜λ⌝-
  NF? {A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) = no λ ()

  NNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NNF t)
  NNF? (var i)          = yes var-
  NNF? (⌜λ⌝ t)          = no λ ()
  NNF? (t₁ ⌜$⌝ t₂)      with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NF t → NF (ren ϱ t)
  renNF ϱ ⌜λ⌝-    = ⌜λ⌝-
  renNF ϱ (nnf p) = nnf (renNNF ϱ p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF t → NNF (ren ϱ t)
  renNNF ϱ var-        = var-
  renNNF ϱ (p₁ ⌜$⌝ p₂) = renNNF ϱ p₁ ⌜$⌝ renNF ϱ p₂

mutual
  nerNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NF (ren ϱ t) → NF t
  nerNF {t = var i}     ϱ (nnf p) = nnf (nerNNF ϱ p)
  nerNF {t = ⌜λ⌝ t}     ϱ ⌜λ⌝-    = ⌜λ⌝-
  nerNF {t = t₁ ⌜$⌝ t₂} ϱ (nnf p) = nnf (nerNNF ϱ p)

  nerNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF (ren ϱ t) → NNF t
  nerNNF {t = var i}     ϱ var-        = var-
  nerNNF {t = t₁ ⌜$⌝ t₂} ϱ (p₁ ⌜$⌝ p₂) = nerNNF ϱ p₁ ⌜$⌝ nerNF ϱ p₂

sub∋NNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NNF (sub∋ σ i)
sub∋NNF {i = zero}  (ψ , p) = p
sub∋NNF {i = wk∋ i} (ψ , p) = sub∋NNF ψ

mutual
  subNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF t → NF (sub σ t)
  subNF ψ ⌜λ⌝-    = ⌜λ⌝-
  subNF ψ (nnf p) = nnf (subNNF ψ p)

  subNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF t → NNF (sub σ t)
  subNNF ψ var-        = sub∋NNF ψ
  subNNF ψ (p₁ ⌜$⌝ p₂) = subNNF ψ p₁ ⌜$⌝ subNF ψ p₂

bus∋NNF : ∀ {A Γ Ξ} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NF (sub∋ σ i) → NF (var i)
bus∋NNF {⌜◦⌝}     {i = i}     ψ        p′   = nnf var-
bus∋NNF {A ⌜⊃⌝ B} {i = zero}  (ψ , ()) ⌜λ⌝-
bus∋NNF {A ⌜⊃⌝ B} {i = wk∋ i} (ψ , p)  p′   with bus∋NNF ψ p′
... | ()

mutual
  busNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NF (sub σ t) → NF t
  busNF {t = var i}     ψ p       = bus∋NNF ψ p
  busNF {t = ⌜λ⌝ t}     ψ ⌜λ⌝-    = ⌜λ⌝-
  busNF {t = t₁ ⌜$⌝ t₂} ψ (nnf p) = nnf (busNNF ψ p)

  busNNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ σ → NNF (sub σ t) → NNF t
  busNNF {t = var i}     ψ p           = var-
  busNNF {t = t₁ ⌜$⌝ t₂} ψ (p₁ ⌜$⌝ p₂) = busNNF ψ p₁ ⌜$⌝ busNF ψ p₂


----------------------------------------------------------------------------------------------------
