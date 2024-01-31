module STLC-Negative-Weak-NotEtaLong where

open import STLC-Negative public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    -⌜,⌝-  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → NF (t₁ ⌜,⌝ t₂)
    ⌜unit⌝ : NF ⌜unit⌝
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-    : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
    _⌜$⌝_   : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜proj₁⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜proj₁⌝ t)
    ⌜proj₂⌝ : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} (p : NNF t) → NNF (⌜proj₂⌝ t)

open NFKit NF NNF public


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝     : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝      : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝    : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$     : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  congproj₁ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₁⌝ t ≝ ⌜proj₁⌝ t′
  congproj₂ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₂⌝ t ≝ ⌜proj₂⌝ t′
  βred⊃     : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) → ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  βred∧₁    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₁⌝ (t₁ ⌜,⌝ t₂) ≝ t₁
  βred∧₂    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₂⌝ (t₁ ⌜,⌝ t₂) ≝ t₂

open ≝Kit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁    : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
              t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂    : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
              t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  congproj₁ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (r : t ⇒ t′) → ⌜proj₁⌝ t ⇒ ⌜proj₁⌝ t′
  congproj₂ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (r : t ⇒ t′) → ⌜proj₂⌝ t ⇒ ⌜proj₂⌝ t′
  βred⊃     : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : NF t₂) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′
  βred∧₁    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₁⌝ (t₁ ⌜,⌝ t₂) ⇒ t₁
  βred∧₂    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₂⌝ (t₁ ⌜,⌝ t₂) ⇒ t₂

open ⇒Kit _⇒_ public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂
  NNF→¬R (⌜proj₁⌝ p) (congproj₁ r)   = r ↯ NNF→¬R p
  NNF→¬R (⌜proj₂⌝ p) (congproj₂ r)   = r ↯ NNF→¬R p

open ¬RKit NF→¬R public


----------------------------------------------------------------------------------------------------

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniNF -⌜,⌝-   -⌜,⌝-    = refl
  uniNF ⌜unit⌝  ⌜unit⌝   = refl
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NNF d) → p ≡ p′
  uniNNF ⌜v⌝-        ⌜v⌝-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜proj₁⌝ p) (⌜proj₁⌝ p′)  = ⌜proj₁⌝ & uniNNF p p′
  uniNNF (⌜proj₂⌝ p) (⌜proj₂⌝ p′)  = ⌜proj₂⌝ & uniNNF p p′

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (congproj₁ r)   (congproj₁ r′)   = congproj₁ & uni⇒ r r′
uni⇒ (congproj₂ r)   (congproj₂ r′)   = congproj₂ & uni⇒ r r′
uni⇒ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′
uni⇒ βred∧₁          βred∧₁           = refl
uni⇒ βred∧₂          βred∧₂           = refl


----------------------------------------------------------------------------------------------------

-- determinism
det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (congproj₁ r)   (congproj₁ r′)   = ⌜proj₁⌝ & det⇒ r r′
det⇒ (congproj₂ r)   (congproj₂ r′)   = ⌜proj₂⌝ & det⇒ r r′
det⇒ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl
det⇒ βred∧₁          βred∧₁           = refl
det⇒ βred∧₂          βred∧₂           = refl

open ⇒*Kit NF→¬R det⇒ uni⇒ public


----------------------------------------------------------------------------------------------------

-- progress
prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (⌜v⌝ i)                = done (nnf ⌜v⌝-)
prog⇒ (⌜λ⌝ t)                = done ⌜λ⌝-
prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _         = step (cong$₁ r₁)
... | done p₁       | step r₂   = step (cong$₂ p₁ r₂)
... | done ⌜λ⌝-     | done p₂   = step (βred⊃ refl p₂)
... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))
prog⇒ (t₁ ⌜,⌝ t₂)              = done -⌜,⌝-
prog⇒ (⌜proj₁⌝ t)            with prog⇒ t
... | step r                    = step (congproj₁ r)
... | done -⌜,⌝-                = step (βred∧₁)
... | done (nnf p)              = done (nnf (⌜proj₁⌝ p))
prog⇒ (⌜proj₂⌝ t)            with prog⇒ t
... | step r                    = step (congproj₂ r)
... | done -⌜,⌝-                = step (βred∧₂)
... | done (nnf p)              = done (nnf (⌜proj₂⌝ p))
prog⇒ ⌜unit⌝                   = done ⌜unit⌝

open ProgKit prog⇒ public

module _ (⚠ : Extensionality) where
  NF≃¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t ≃ (¬ RF t)
  NF≃¬RF = record
    { to      = NF→¬RF
    ; from    = ¬RF→NF
    ; from∘to = λ p → uniNF _ p
    ; to∘from = λ p → uni¬RF ⚠ _ p
    }


----------------------------------------------------------------------------------------------------

-- stability under renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-    = ⌜λ⌝-
  renNF e -⌜,⌝-   = -⌜,⌝-
  renNF e ⌜unit⌝  = ⌜unit⌝
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e ⌜v⌝-        = ⌜v⌝-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂
  renNNF e (⌜proj₁⌝ p) = ⌜proj₁⌝ (renNNF e p)
  renNNF e (⌜proj₂⌝ p) = ⌜proj₂⌝ (renNNF e p)

-- ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒ t′ → ren e t ⇒ ren e t′
-- ren⇒ e (cong$₁ r₁)               = cong$₁ (ren⇒ e r₁)
-- ren⇒ e (cong$₂ p₁ r₂)            = cong$₂ (renNF e p₁) (ren⇒ e r₂)
-- ren⇒ e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (renβred⊃ e t₁ _ ⁻¹) (renNF e p₂)


----------------------------------------------------------------------------------------------------
