----------------------------------------------------------------------------------------------------

-- β-short η-long expanded weak normal form

module STLC-Base-EWNF where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) →
            NNF (t₁ ⌜$⌝ t₂)

-- TODO: kit
data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  []  : NNF§ []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢§ Δ} → NNF t → NNF§ ts → NNF§ (t ∷ ts)

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
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-    = ⌜λ⌝-
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-        = var-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂

mutual
  nerNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF (ren e t) → NF t
  nerNF {t = var i}     e (nnf p) = nnf (nerNNF e p)
  nerNF {t = ⌜λ⌝ t}     e ⌜λ⌝-    = ⌜λ⌝-
  nerNF {t = t₁ ⌜$⌝ t₂} e (nnf p) = nnf (nerNNF e p)

  nerNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF (ren e t) → NNF t
  nerNNF {t = var i}     e var-        = var-
  nerNNF {t = t₁ ⌜$⌝ t₂} e (p₁ ⌜$⌝ p₂) = nerNNF e p₁ ⌜$⌝ nerNF e p₂

sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NF t → NF (sub ss t)
  subNF ps ⌜λ⌝-    = ⌜λ⌝-
  subNF ps (nnf p) = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NNF t → NNF (sub ss t)
  subNNF ps var-        = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂) = subNNF ps p₁ ⌜$⌝ subNF ps p₂

bus∋NNF : ∀ {A Γ Ξ} {ss : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ ss → NF (sub∋ ss i) → NF (var i)
bus∋NNF {⌜◦⌝}     {i = i}     ps        p′   = nnf var-
bus∋NNF {A ⌜⊃⌝ B} {i = zero}  (() ∷ ps) ⌜λ⌝-
bus∋NNF {A ⌜⊃⌝ B} {i = suc i} (p ∷ ps)  p′   with bus∋NNF ps p′
... | ()

mutual
  busNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NF (sub ss t) → NF t
  busNF {t = var i}     ps p       = bus∋NNF ps p
  busNF {t = ⌜λ⌝ t}     ps ⌜λ⌝-    = ⌜λ⌝-
  busNF {t = t₁ ⌜$⌝ t₂} ps (nnf p) = nnf (busNNF ps p)

  busNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t : Γ ⊢ A} → NNF§ ss → NNF (sub ss t) → NNF t
  busNNF {t = var i}     ps p           = var-
  busNNF {t = t₁ ⌜$⌝ t₂} ps (p₁ ⌜$⌝ p₂) = busNNF ps p₁ ⌜$⌝ busNF ps p₂


----------------------------------------------------------------------------------------------------
