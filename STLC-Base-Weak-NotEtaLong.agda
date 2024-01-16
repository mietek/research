module STLC-Base-Weak-NotEtaLong where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `λ   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (`λ t)
    `nnf : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `v   : ∀ {A} {i : Γ ∋ A} → NNF (`v i)
    _`$_ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ `$ t₂)

-- TODO: delete?
-- -- decidability
-- mutual
--   NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
--   NF? (`v i)            = yes (`nnf `v)
--   NF? (`λ t)            = yes `λ
--   NF? (t₁ `$ t₂)        with NNF? t₁ | NF? t₂
--   ... | no ¬p₁ | _        = no λ { (`nnf (p₁ `$ p₂)) → p₁ ↯ ¬p₁ }
--   ... | yes p₁ | no ¬p₂   = no λ { (`nnf (p₁ `$ p₂)) → p₂ ↯ ¬p₂ }
--   ... | yes p₁ | yes p₂   = yes (`nnf (p₁ `$ p₂))
--
--   NNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NNF t)
--   NNF? (`v i)           = yes `v
--   NNF? (`λ t)           = no λ ()
--   NNF? (t₁ `$ t₂)       with NNF? t₁ | NF? t₂
--   ... | no ¬p₁ | _        = no λ { (p₁ `$ p₂) → p₁ ↯ ¬p₁ }
--   ... | yes p₁ | no ¬p₂   = no λ { (p₁ `$ p₂) → p₂ ↯ ¬p₂ }
--   ... | yes p₁ | yes p₂   = yes (p₁ `$ p₂)

-- renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e `λ       = `λ
  renNF e (`nnf p) = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e `v         = `v
  renNNF e (p₁ `$ p₂) = renNNF e p₁ `$ renNF e p₂

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF `λ       `λ        = refl
  uniNF (`nnf p) (`nnf p′) = `nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF `v         `v           = refl
  uniNNF (p₁ `$ p₂) (p₁′ `$ p₂′) = _`$_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ `$ t₂ ≝ t₁′ `$ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           `λ t₁ `$ t₂ ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒ t₁′) →
           t₁ `$ t₂ ⇒ t₁′ `$ t₂
  cong$₂ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
           t₁ `$ t₂ ⇒ t₁ `$ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
             (p₂ : NF t₂) →
           `λ t₁ `$ t₂ ⇒ t′

open ⇒Kit _⇒_ public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (`nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ `$ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ `$ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂

-- progress
prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog NF t
prog⇒ (`v i)                  = done (`nnf `v)
prog⇒ (`λ t)                  = done `λ
prog⇒ (t₁ `$ t₂)              with prog⇒ t₁ | prog⇒ t₂
... | step r₁        | _         = step (cong$₁ r₁)
... | done p₁        | step r₂   = step (cong$₂ p₁ r₂)
... | done `λ        | done p₂   = step (βred⊃ refl p₂)
... | done (`nnf p₁) | done p₂   = done (`nnf (p₁ `$ p₂))

open ProgKit NF→¬R prog⇒ public

-- determinism
det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = (_`$ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ `$_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl

open DetKit NF→¬R det⇒ public

-- uniqueness of proofs
uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′


----------------------------------------------------------------------------------------------------
