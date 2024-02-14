----------------------------------------------------------------------------------------------------

-- β-short normal forms

module STLC-Base-NF where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝ : ∀ {A B} {t : A ∷ Γ ⊢ B} (p : NF t) → NF (⌜λ⌝ t)
    nnf : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  []  : NNF§ []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢§ Δ} → NNF t → NNF§ ts → NNF§ (t ∷ ts)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (⌜λ⌝ p) (⌜λ⌝ p′) = ⌜λ⌝ & uniNF p p′
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-        var-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′


----------------------------------------------------------------------------------------------------

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊑ Γ′) → NF t → NF (ren e t)
  renNF e (⌜λ⌝ p) = ⌜λ⌝ (renNF (lift⊑ e) p)
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊑ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-        = var-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂

-- TODO: kit
renNNF§ : ∀ {Γ Γ′ Δ} {ss : Γ ⊢§ Δ} (e : Γ ⊑ Γ′) → NNF§ ss → NNF§ (ren§ e ss)
renNNF§ e []       = []
renNNF§ e (p ∷ ps) = renNNF e p ∷ renNNF§ e ps

wkNNF§ : ∀ {B Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (wk§ {B} ss)
wkNNF§ ps = renNNF§ (wk⊑ id⊑) ps

liftNNF§ : ∀ {B Γ Δ} {ss : Γ ⊢§ Δ} → NNF§ ss → NNF§ (lift§ {B} ss)
liftNNF§ ps = var- ∷ wkNNF§ ps

sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NF t → NF (sub ss t)
  subNF ps (⌜λ⌝ p) = ⌜λ⌝ (subNF (liftNNF§ ps) p)
  subNF ps (nnf p) = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NNF t → NNF (sub ss t)
  subNNF ps var-        = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂) = subNNF ps p₁ ⌜$⌝ subNF ps p₂


----------------------------------------------------------------------------------------------------
