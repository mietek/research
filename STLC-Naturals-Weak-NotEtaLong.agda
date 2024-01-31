module STLC-Naturals-Weak-NotEtaLong where

open import STLC-Naturals public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long semi-weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF ⌜zero⌝
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜suc⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NNF tₙ) (p₀ : NF t₀)
              (p₁ : NF t₁) →
            NNF (⌜rec⌝ tₙ t₀ t₁)

open NFKit NF NNF public


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
            t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  congrec : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ tₛ′ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A}
              (eqₙ : tₙ ≝ tₙ′) (eq₀ : t₀ ≝ t₀′) (eqₛ : tₛ ≝ tₛ′) →
            ⌜rec⌝ tₙ t₀ tₛ ≝ ⌜rec⌝ tₙ′ t₀′ tₛ′
  βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
            ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  βredℕ₀  : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} → ⌜rec⌝ ⌜zero⌝ t₀ tₛ ≝ t₀
  βredℕₛ  : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} {t′ : Γ ⊢ A}
              (eq : t′ ≡ tₛ [ tₙ ∣ ⌜rec⌝ tₙ t₀ tₛ ]) →
            ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ≝ t′

open ≝Kit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂   : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  congsuc  : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (r : t ⇒ t′) → ⌜suc⌝ t ⇒ ⌜suc⌝ t′
  congrecₙ : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (rₙ : tₙ ⇒ tₙ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ′ t₀ tₛ
  congrec₀ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NF tₙ)
               (r₀ : t₀ ⇒ t₀′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀′ tₛ
  congrecₛ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ tₛ′ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NF tₙ)
               (p₀ : NF t₀) (rₛ : tₛ ⇒ tₛ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀ tₛ′
  βred⊃    : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
               (p₂ : NF t₂) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′
  βredℕ₀   : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (p₀ : NF t₀) (pₛ : NF tₛ) →
             ⌜rec⌝ ⌜zero⌝ t₀ tₛ ⇒ t₀
  βredℕₛ   : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} {t′ : Γ ⊢ A}
               (eq : t′ ≡ tₛ [ tₙ ∣ ⌜rec⌝ tₙ t₀ tₛ ]) (pₙ : NF (⌜suc⌝ tₙ)) (p₀ : NF t₀)
               (pₛ : NF tₛ) →
             ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ⇒ t′

open ⇒Kit _⇒_ public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (⌜suc⌝ p) (congsuc r) = r ↯ NF→¬R p
  NF→¬R (nnf p) r           = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂)      (cong$₁ r₁)           = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂)      (cong$₂ p₁′ r₂)       = r₂ ↯ NF→¬R p₂
  NNF→¬R (() ⌜$⌝ p₂)      (βred⊃ eq p₂′)
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrecₙ rₙ)         = rₙ ↯ NNF→¬R pₙ
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrec₀ pₙ′ r₀)     = r₀ ↯ NF→¬R p₀
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrecₛ pₙ′ p₀′ rₛ) = rₛ ↯ NF→¬R pₛ

open ¬RKit NF→¬R public


----------------------------------------------------------------------------------------------------

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-      ⌜λ⌝-       = refl
  uniNF ⌜zero⌝    ⌜zero⌝     = refl
  uniNF (⌜suc⌝ p) (⌜suc⌝ p′) = ⌜suc⌝ & uniNF p p′
  uniNF (nnf p)   (nnf p′)   = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF ⌜v⌝-             ⌜v⌝-                = refl
  uniNNF (p₁ ⌜$⌝ p₂)      (p₁′ ⌜$⌝ p₂′)       = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜rec⌝ pₙ p₀ pₛ) (⌜rec⌝ pₙ′ p₀′ pₛ′) = ⌜rec⌝ & uniNNF pₙ pₙ′ ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)            (cong$₁ r₁′)              = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)            (cong$₂ p₁′ r₂′)          = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)         (cong$₁ r₁′)              = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)         (cong$₂ p₁′ r₂′)          = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)         (βred⊃ eq′ p₂)            = r₂ ↯ NF→¬R p₂
uni⇒ (congsuc r)            (congsuc r′)              = congsuc & uni⇒ r r′
uni⇒ (congrecₙ rₙ)          (congrecₙ rₙ′)            = congrecₙ & uni⇒ rₙ rₙ′
uni⇒ (congrecₙ rₙ)          (congrec₀ pₙ′ r₀′)        = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrecₙ rₙ)          (congrecₛ pₙ′ p₀′ rₛ′)    = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrecₙ rₙ)          (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrec₀ pₙ r₀)       (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (congrec₀ pₙ r₀)       (congrec₀ pₙ′ r₀′)        = congrec₀ & uniNF pₙ pₙ′ ⊗ uni⇒ r₀ r₀′
uni⇒ (congrec₀ pₙ r₀)       (congrecₛ pₙ′ p₀′ rₛ′)    = r₀ ↯ NF→¬R p₀′
uni⇒ (congrec₀ pₙ r₀)       (βredℕ₀ p₀′ pₛ′)          = r₀ ↯ NF→¬R p₀′
uni⇒ (congrec₀ pₙ r₀)       (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = r₀ ↯ NF→¬R p₀′
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₛ pₙ′ p₀′ rₛ′)    = _ & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀′
                                                           ⊗ uni⇒ rₛ rₛ′
uni⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = rₛ ↯ NF→¬R pₛ′
uni⇒ (βred⊃ eq p₂)          (cong$₂ p₁′ r₂′)          = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂)        (βred⊃ refl p₂′)          = βred⊃ refl & uniNF p₂ p₂′
uni⇒ (βredℕ₀ p₀ pₛ)         (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (βredℕ₀ p₀ pₛ)         (βredℕ₀ p₀′ pₛ′)          = βredℕ₀ & uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
uni⇒ (βredℕₛ refl pₙ p₀ pₛ) (βredℕₛ refl pₙ′ p₀′ pₛ′) = βredℕₛ refl & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀′
                                                           ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

-- determinism
det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)            (cong$₁ r₁′)              = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)            (cong$₂ p₁′ r₂′)          = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)         (cong$₁ r₁′)              = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)         (cong$₂ p₁′ r₂′)          = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)         (βred⊃ refl p₂′)          = r₂ ↯ NF→¬R p₂′
det⇒ (congsuc r)            (congsuc r′)              = ⌜suc⌝ & det⇒ r r′
det⇒ (congrecₙ rₙ)          (congrecₙ rₙ′)            = _ & det⇒ rₙ rₙ′
det⇒ (congrecₙ rₙ)          (congrec₀ pₙ′ r₀′)        = rₙ ↯ NF→¬R pₙ′
det⇒ (congrecₙ rₙ)          (congrecₛ pₙ′ p₀′ rₛ′)    = rₙ ↯ NF→¬R pₙ′
det⇒ (congrecₙ rₙ)          (βredℕₛ refl pₙ′ p₀′ pₛ′) = rₙ ↯ NF→¬R pₙ′
det⇒ (congrec₀ pₙ r₀)       (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (congrec₀ pₙ r₀)       (congrec₀ pₙ′ r₀′)        = _ & uniNF pₙ pₙ′ ⊗ det⇒ r₀ r₀′
det⇒ (congrec₀ pₙ r₀)       (congrecₛ pₙ′ p₀′ rₛ′)    = r₀ ↯ NF→¬R p₀′
det⇒ (congrec₀ pₙ r₀)       (βredℕ₀ p₀′ pₛ′)          = r₀ ↯ NF→¬R p₀′
det⇒ (congrec₀ pₙ r₀)       (βredℕₛ refl pₙ′ p₀′ pₛ′) = r₀ ↯ NF→¬R p₀′
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₛ pₙ′ p₀′ rₛ′)    = _ & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀
                                                           ⊗ det⇒ rₛ rₛ′
det⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕ₀ p₀′ pₛ′)          = rₛ ↯ NF→¬R pₛ′
det⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕₛ refl pₙ′ p₀′ pₛ′) = rₛ ↯ NF→¬R pₛ′
det⇒ (βred⊃ refl p₂)        (cong$₂ p₁′ r₂′)          = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂)        (βred⊃ refl p₂′)          = refl
det⇒ (βredℕ₀ p₀ pₛ)         (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (βredℕ₀ p₀ pₛ)         (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
det⇒ (βredℕ₀ p₀ pₛ)         (βredℕ₀ p₀′ pₛ′)          = refl
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (βredℕₛ refl pₙ′ p₀′ pₛ′) = refl

open ⇒*Kit NF→¬R det⇒ uni⇒ public


----------------------------------------------------------------------------------------------------

-- progress
prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (⌜v⌝ i)                            = done (nnf ⌜v⌝-)
prog⇒ (⌜λ⌝ t)                            = done ⌜λ⌝-
prog⇒ (t₁ ⌜$⌝ t₂)                        with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _                     = step (cong$₁ r₁)
... | done p₁       | step r₂               = step (cong$₂ p₁ r₂)
... | done ⌜λ⌝-     | done p₂               = step (βred⊃ refl p₂)
... | done (nnf p₁) | done p₂               = done (nnf (p₁ ⌜$⌝ p₂))
prog⇒ ⌜zero⌝                             = done ⌜zero⌝
prog⇒ (⌜suc⌝ t)                          with prog⇒ t
... | step r                                = step (congsuc r)
... | done p                                = done (⌜suc⌝ p)
prog⇒ (⌜rec⌝ tₙ t₀ tₛ)                   with prog⇒ tₙ | prog⇒ t₀ | prog⇒ tₛ
... | step rₙ         | _       | _         = step (congrecₙ rₙ)
... | done pₙ         | step r₀ | _         = step (congrec₀ pₙ r₀)
... | done pₙ         | done p₀ | step rₛ   = step (congrecₛ pₙ p₀ rₛ)
... | done ⌜zero⌝     | done p₀ | done pₛ   = step (βredℕ₀ p₀ pₛ)
... | done (⌜suc⌝ pₙ) | done p₀ | done pₛ   = step (βredℕₛ refl (⌜suc⌝ pₙ) p₀ pₛ)
... | done (nnf pₙ)   | done p₀ | done pₛ   = done (nnf (⌜rec⌝ pₙ p₀ pₛ))

open ProgKit prog⇒ public hiding (NF?)

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
  renNF e ⌜λ⌝-      = ⌜λ⌝-
  renNF e ⌜zero⌝    = ⌜zero⌝
  renNF e (⌜suc⌝ p) = ⌜suc⌝ (renNF e p)
  renNF e (nnf p)   = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e ⌜v⌝-             = ⌜v⌝-
  renNNF e (p₁ ⌜$⌝ p₂)      = renNNF e p₁ ⌜$⌝ renNF e p₂
  renNNF e (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF e pₙ) (renNF e p₀) (renNF (keep (keep e)) pₛ)


----------------------------------------------------------------------------------------------------
