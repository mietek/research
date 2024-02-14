----------------------------------------------------------------------------------------------------

-- β-short semi-weak normal form

module STLC-Naturals-SWNF where

open import STLC-Naturals public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF ⌜zero⌝
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜suc⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NNF tₙ) (p₀ : NF t₀)
              (p₁ : NF t₁) →
            NNF (⌜rec⌝ tₙ t₀ t₁)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  []  : NNF§ []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢§ Δ} → NNF t → NNF§ ts → NNF§ (t ∷ ts)

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
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-      = ⌜λ⌝-
  renNF e ⌜zero⌝    = ⌜zero⌝
  renNF e (⌜suc⌝ p) = ⌜suc⌝ (renNF e p)
  renNF e (nnf p)   = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-             = var-
  renNNF e (p₁ ⌜$⌝ p₂)      = renNNF e p₁ ⌜$⌝ renNF e p₂
  renNNF e (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF e pₙ) (renNF e p₀) (renNF (lift⊆² e) pₛ)

-- TODO: kit
renNNF§ : ∀ {Γ Γ′ Δ} {ss : Γ ⊢§ Δ} (e : Γ ⊆ Γ′) → NNF§ ss → NNF§ (ren§ e ss)
renNNF§ e []       = []
renNNF§ e (p ∷ ps) = renNNF e p ∷ renNNF§ e ps

wkNNF§ : ∀ {B Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (wk§ {B} ss)
wkNNF§ ps = renNNF§ (wk⊆ id⊆) ps

wkNNF§² : ∀ {B C Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (wk§² {B} {C} ss)
wkNNF§² = wkNNF§ ∘ wkNNF§

liftNNF§ : ∀ {B Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (lift§ {B} ss)
liftNNF§ ps = var- ∷ wkNNF§ ps

liftNNF§² : ∀ {B C Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (lift§² {B} {C} ss)
liftNNF§² = liftNNF§ ∘ liftNNF§

sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NF t → NF (sub ss t)
  subNF ps ⌜λ⌝-      = ⌜λ⌝-
  subNF ps ⌜zero⌝    = ⌜zero⌝
  subNF ps (⌜suc⌝ p) = ⌜suc⌝ (subNF ps p)
  subNF ps (nnf p)   = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NNF t → NNF (sub ss t)
  subNNF ps var-             = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂)      = subNNF ps p₁ ⌜$⌝ subNF ps p₂
  subNNF ps (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (subNNF ps pₙ) (subNF ps p₀) (subNF (liftNNF§² ps) pₛ)


----------------------------------------------------------------------------------------------------
