module STLC-Base-EWNF where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms
mutual
  data FNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → FNF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : FNNF t) → FNF t

  data FNNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → FNNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : FNNF t₁) (p₂ : FNF t₂) →
            FNNF (t₁ ⌜$⌝ t₂)

data FNNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : FNNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → FNNF t → FNNF* ts → FNNF* (t ∷ ts)

mutual
  uniFNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNF t) → p ≡ p′
  uniFNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniFNF (nnf p) (nnf p′) = nnf & uniFNNF p p′

  uniFNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNNF t) → p ≡ p′
  uniFNNF var-        var-          = refl
  uniFNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

mutual
  FNF? : ∀ {A Γ} (t : Γ ⊢ A) → Dec (FNF t)
  FNF? {⌜◦⌝}     (var i)     = yes (nnf var-)
  FNF? {⌜◦⌝}     (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂        = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂        = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _             = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
  FNF? {A ⌜⊃⌝ B} (var i)     = no λ ()
  FNF? {A ⌜⊃⌝ B} (⌜λ⌝ t)     = yes ⌜λ⌝-
  FNF? {A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) = no λ ()

  FNNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNNF t)
  FNNF? (var i)         = yes var-
  FNNF? (⌜λ⌝ t)         = no λ ()
  FNNF? (t₁ ⌜$⌝ t₂)     with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

mutual
  renFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF t → FNF (ren e t)
  renFNF e ⌜λ⌝-    = ⌜λ⌝-
  renFNF e (nnf p) = nnf (renFNNF e p)

  renFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF t → FNNF (ren e t)
  renFNNF e var-        = var-
  renFNNF e (p₁ ⌜$⌝ p₂) = renFNNF e p₁ ⌜$⌝ renFNF e p₂

mutual
  nerFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF (ren e t) → FNF t
  nerFNF {t = var i}     e (nnf p) = nnf (nerFNNF e p)
  nerFNF {t = ⌜λ⌝ t}     e ⌜λ⌝-    = ⌜λ⌝-
  nerFNF {t = t₁ ⌜$⌝ t₂} e (nnf p) = nnf (nerFNNF e p)

  nerFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF (ren e t) → FNNF t
  nerFNNF {t = var i}     e var-        = var-
  nerFNNF {t = t₁ ⌜$⌝ t₂} e (p₁ ⌜$⌝ p₂) = nerFNNF e p₁ ⌜$⌝ nerFNF e p₂

sub∋FNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → FNNF* ss → FNNF (sub∋ ss i)
sub∋FNNF {i = zero}  (p ∷ ps) = p
sub∋FNNF {i = suc i} (p ∷ ps) = sub∋FNNF ps

mutual
  subFNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNF t → FNF (sub ss t)
  subFNF ps ⌜λ⌝-    = ⌜λ⌝-
  subFNF ps (nnf p) = nnf (subFNNF ps p)

  subFNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNNF t → FNNF (sub ss t)
  subFNNF ps var-        = sub∋FNNF ps
  subFNNF ps (p₁ ⌜$⌝ p₂) = subFNNF ps p₁ ⌜$⌝ subFNF ps p₂

bus∋FNNF : ∀ {A Γ Ξ} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → FNNF* ss → FNF (sub∋ ss i) → FNF (var i)
bus∋FNNF {⌜◦⌝}     {i = i}     ps        p′   = nnf var-
bus∋FNNF {A ⌜⊃⌝ B} {i = zero}  (() ∷ ps) ⌜λ⌝-
bus∋FNNF {A ⌜⊃⌝ B} {i = suc i} (p ∷ ps)  p′   with bus∋FNNF ps p′
... | ()

mutual
  busFNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNF (sub ss t) → FNF t
  busFNF {t = var i}     ps p       = bus∋FNNF ps p
  busFNF {t = ⌜λ⌝ t}     ps ⌜λ⌝-    = ⌜λ⌝-
  busFNF {t = t₁ ⌜$⌝ t₂} ps (nnf p) = nnf (busFNNF ps p)

  busFNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNNF (sub ss t) → FNNF t
  busFNNF {t = var i}     ps p           = var-
  busFNNF {t = t₁ ⌜$⌝ t₂} ps (p₁ ⌜$⌝ p₂) = busFNNF ps p₁ ⌜$⌝ busFNF ps p₂


----------------------------------------------------------------------------------------------------
