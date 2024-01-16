module STLC-Naturals-Weak-NotEtaLong where

open import STLC-Naturals public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `λ    : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (`λ t)
    `zero : NF (`zero)
    `suc  : ∀ {t : Γ ⊢ `ℕ} → NF (`suc t)
    `nnf  : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `v   : ∀ {A} {i : Γ ∋ A} → NNF (`v i)
    _`$_ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ `$ t₂)
    `rec : ∀ {A} {t₁ : Γ ⊢ `ℕ} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NNF t₁)
             (p₂ : NF t₂) (p₃ : NF t₃) →
           NNF (`rec t₁ t₂ t₃)

-- renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e `λ       = `λ
  renNF e `zero    = `zero
  renNF e `suc     = `suc
  renNF e (`nnf p) = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e `v              = `v
  renNNF e (p₁ `$ p₂)      = renNNF e p₁ `$ renNF e p₂
  renNNF e (`rec p₁ p₂ p₃) = `rec (renNNF e p₁) (renNF e p₂) (renNF (keep (keep e)) p₃)

-- NF and NNF have unique proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF `λ       `λ        = refl
  uniNF `zero    `zero     = refl
  uniNF `suc     `suc      = refl
  uniNF (`nnf p) (`nnf p′) = `nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF `v              `v                 = refl
  uniNNF (p₁ `$ p₂)      (p₁′ `$ p₂′)       = _`$_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (`rec p₁ p₂ p₃) (`rec p₁′ p₂′ p₃′) = `rec & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
            t₁ `$ t₂ ≝ t₁′ `$ t₂′
  congrec : ∀ {A} {t₁ t₁′ : Γ ⊢ `ℕ} {t₂ t₂′ : Γ ⊢ A} {t₃ t₃′ : A ∷ `ℕ ∷ Γ ⊢ A}
              (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) (eq₃ : t₃ ≝ t₃′) →
            `rec t₁ t₂ t₃ ≝ `rec t₁′ t₂′ t₃′
  βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
            `λ t₁ `$ t₂ ≝ t′
  βredℕ₁  : ∀ {A} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} → `rec `zero t₂ t₃ ≝ t₂
  βredℕ₂  : ∀ {A} {t₁ : Γ ⊢ `ℕ} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} {t′ : Γ ⊢ A}
              (eq : t′ ≡ t₃ [ t₁ ∣ `rec t₁ t₂ t₃ ]) →
            `rec (`suc t₁) t₂ t₃ ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
             t₁ `$ t₂ ⇒ t₁′ `$ t₂
  cong$₂   : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
             t₁ `$ t₂ ⇒ t₁ `$ t₂′
  congrec₁ : ∀ {A} {t₁ t₁′ : Γ ⊢ `ℕ} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
             `rec t₁ t₂ t₃ ⇒ `rec t₁′ t₂ t₃
  congrec₂ : ∀ {A} {t₁ : Γ ⊢ `ℕ} {t₂ t₂′ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NF t₁)
               (r₂ : t₂ ⇒ t₂′) →
             `rec t₁ t₂ t₃ ⇒ `rec t₁ t₂′ t₃
  congrec₃ : ∀ {A} {t₁ : Γ ⊢ `ℕ} {t₂ : Γ ⊢ A} {t₃ t₃′ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NF t₁)
               (p₂ : NF t₂) (r₃ : t₃ ⇒ t₃′) →
             `rec t₁ t₂ t₃ ⇒ `rec t₁ t₂ t₃′
  βred⊃    : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
               (p₂ : NF t₂) →
             `λ t₁ `$ t₂ ⇒ t′
  βredℕ₁   : ∀ {A} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₂ : NF t₂) (p₃ : NF t₃) →
             `rec `zero t₂ t₃ ⇒ t₂
  βredℕ₂   : ∀ {A} {t₁ : Γ ⊢ `ℕ} {t₂ : Γ ⊢ A} {t₃ : A ∷ `ℕ ∷ Γ ⊢ A} {t′ : Γ ⊢ A}
               (eq : t′ ≡ t₃ [ t₁ ∣ `rec t₁ t₂ t₃ ]) (p₂ : NF t₂) (p₃ : NF t₃) →
             `rec (`suc t₁) t₂ t₃ ⇒ t′

open ⇒Kit _⇒_ public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (`nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ `$ p₂)      (cong$₁ r₁)           = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ `$ p₂)      (cong$₂ p₁′ r₂)       = r₂ ↯ NF→¬R p₂
  NNF→¬R (() `$ p₂)      (βred⊃ eq p₂′)
  NNF→¬R (`rec p₁ p₂ p₃) (congrec₁ r₁)         = r₁ ↯ NNF→¬R p₁
  NNF→¬R (`rec p₁ p₂ p₃) (congrec₂ p₁′ r₂)     = r₂ ↯ NF→¬R p₂
  NNF→¬R (`rec p₁ p₂ p₃) (congrec₃ p₁′ p₂′ r₃) = r₃ ↯ NF→¬R p₃

-- progress
prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog NF t
prog⇒ (`v i)                             = done (`nnf `v)
prog⇒ (`λ t)                             = done `λ
prog⇒ (t₁ `$ t₂)                         with prog⇒ t₁ | prog⇒ t₂
... | step r₁        | _                     = step (cong$₁ r₁)
... | done p₁        | step r₂               = step (cong$₂ p₁ r₂)
... | done `λ        | done p₂               = step (βred⊃ refl p₂)
... | done (`nnf p₁) | done p₂               = done (`nnf (p₁ `$ p₂))
prog⇒ `zero                              = done `zero
prog⇒ (`suc t)                           = done `suc
prog⇒ (`rec t₁ t₂ t₃)                    with prog⇒ t₁ | prog⇒ t₂ | prog⇒ t₃
... | step r₁         | _       | _         = step (congrec₁ r₁)
... | done p₁         | step r₂ | _         = step (congrec₂ p₁ r₂)
... | done p₁         | done p₂ | step r₃   = step (congrec₃ p₁ p₂ r₃)
... | done `zero      | done p₂ | done p₃   = step (βredℕ₁ p₂ p₃)
... | done `suc       | done p₂ | done p₃   = step (βredℕ₂ refl p₂ p₃)
... | done (`nnf p₁)  | done p₂ | done p₃   = done (`nnf (`rec p₁ p₂ p₃))

open ProgKit NF→¬R prog⇒ public

-- determinism
det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)         (cong$₁ r₁′)           = (_`$ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)         (cong$₂ p₁′ r₂′)       = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)      (cong$₁ r₁′)           = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)      (cong$₂ p₁′ r₂′)       = (_ `$_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)      (βred⊃ refl p₂′)       = r₂ ↯ NF→¬R p₂′
det⇒ (congrec₁ r₁)       (congrec₁ r₁′)         = _ & det⇒ r₁ r₁′
det⇒ (congrec₁ r₁)       (congrec₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
det⇒ (congrec₁ r₁)       (congrec₃ p₁′ p₂′ r₃′) = r₁ ↯ NF→¬R p₁′
det⇒ (congrec₂ p₁ r₂)    (congrec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
det⇒ (congrec₂ p₁ r₂)    (congrec₂ p₁′ r₂′)     = _ & uniNF p₁ p₁′ ⊗ det⇒ r₂ r₂′
det⇒ (congrec₂ p₁ r₂)    (congrec₃ p₁′ p₂′ r₃′) = r₂ ↯ NF→¬R p₂′
det⇒ (congrec₂ p₁ r₂)    (βredℕ₁ p₂′ p₃′)       = r₂ ↯ NF→¬R p₂′
det⇒ (congrec₂ p₁ r₂)    (βredℕ₂ refl p₂′ p₃′)  = r₂ ↯ NF→¬R p₂′
det⇒ (congrec₃ p₁ p₂ r₃) (congrec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
det⇒ (congrec₃ p₁ p₂ r₃) (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⇒ (congrec₃ p₁ p₂ r₃) (congrec₃ p₁′ p₂′ r₃′) = _ & uniNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗ det⇒ r₃ r₃′
det⇒ (congrec₃ p₁ p₂ r₃) (βredℕ₁ p₂′ p₃′)       = r₃ ↯ NF→¬R p₃′
det⇒ (congrec₃ p₁ p₂ r₃) (βredℕ₂ refl p₂′ p₃′)  = r₃ ↯ NF→¬R p₃′
det⇒ (βred⊃ refl p₂)     (cong$₂ p₁′ r₂′)       = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂)     (βred⊃ refl p₂′)       = refl
det⇒ (βredℕ₁ p₂ p₃)      (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⇒ (βredℕ₁ p₂ p₃)      (congrec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
det⇒ (βredℕ₁ p₂ p₃)      (βredℕ₁ p₂′ p₃′)       = refl
det⇒ (βredℕ₂ refl p₂ p₃) (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⇒ (βredℕ₂ refl p₂ p₃) (congrec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
det⇒ (βredℕ₂ refl p₂ p₃) (βredℕ₂ refl p₂′ p₃′)  = refl

open DetKit NF→¬R det⇒ public

-- uniqueness of proofs
uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)         (cong$₁ r₁′)           = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)         (cong$₂ p₁′ r₂′)       = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)      (cong$₁ r₁′)           = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)      (cong$₂ p₁′ r₂′)       = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)      (βred⊃ eq′ p₂)         = r₂ ↯ NF→¬R p₂
uni⇒ (congrec₁ r₁)       (congrec₁ r₁′)         = congrec₁ & uni⇒ r₁ r₁′
uni⇒ (congrec₁ r₁)       (congrec₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
uni⇒ (congrec₁ r₁)       (congrec₃ p₁′ p₂′ r₃′) = r₁ ↯ NF→¬R p₁′
uni⇒ (congrec₂ p₁ r₂)    (congrec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
uni⇒ (congrec₂ p₁ r₂)    (congrec₂ p₁′ r₂′)     = congrec₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (congrec₂ p₁ r₂)    (congrec₃ p₁′ p₂′ r₃′) = r₂ ↯ NF→¬R p₂′
uni⇒ (congrec₂ p₁ r₂)    (βredℕ₁ p₂′ p₃′)       = r₂ ↯ NF→¬R p₂′
uni⇒ (congrec₂ p₁ r₂)    (βredℕ₂ eq′ p₂′ p₃′)   = r₂ ↯ NF→¬R p₂′
uni⇒ (congrec₃ p₁ p₂ r₃) (congrec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
uni⇒ (congrec₃ p₁ p₂ r₃) (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⇒ (congrec₃ p₁ p₂ r₃) (congrec₃ p₁′ p₂′ r₃′) = _ & uniNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗ uni⇒ r₃ r₃′
uni⇒ (congrec₃ p₁ p₂ r₃) (βredℕ₂ eq′ p₂′ p₃′)   = r₃ ↯ NF→¬R p₃′
uni⇒ (βred⊃ eq p₂)       (cong$₂ p₁′ r₂′)       = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂)     (βred⊃ refl p₂′)       = βred⊃ refl & uniNF p₂ p₂′
uni⇒ (βredℕ₁ p₂ p₃)      (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⇒ (βredℕ₁ p₂ p₃)      (βredℕ₁ p₂′ p₃′)       = βredℕ₁ & uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′
uni⇒ (βredℕ₂ eq p₂ p₃)   (congrec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⇒ (βredℕ₂ eq p₂ p₃)   (congrec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
uni⇒ (βredℕ₂ refl p₂ p₃) (βredℕ₂ refl p₂′ p₃′)  = βredℕ₂ refl & uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′


----------------------------------------------------------------------------------------------------
