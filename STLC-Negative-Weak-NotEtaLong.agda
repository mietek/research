module STLC-Negative-Weak-NotEtaLong where

open import STLC-Negative public


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short not-η-long weak normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ    : ∀ {A B} (d : A ∷ Γ ⊢ B) → NF (`λ d)
    _`,_  : ∀ {A B} (d₁ : Γ ⊢ A) (d₂ : Γ ⊢ B) → NF (d₁ `, d₂)
    `unit : NF `unit
    `nnf  : ∀ {A} {d : Γ ⊢ A} (p : NNF d) → NF d

  -- d is in neutral β-short not-η-long weak normal form
  data NNF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `v     : ∀ {A} (i : Γ ∋ A) → NNF (`v i)
    _`$_   : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (p₁ : NNF d₁) (p₂ : NF d₂) → NNF (d₁ `$ d₂)
    `proj₁ : ∀ {A B} {d : Γ ⊢ A `∧ B} (p : NNF d) → NNF (`proj₁ d)
    `proj₂ : ∀ {A B} {d : Γ ⊢ A `∧ B} (p : NNF d) → NNF (`proj₂ d)

-- NF and NNF have unique proofs
mutual
  uniNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NF d) → p ≡ p′
  uniNF (`λ d)     (`λ .d)      = refl
  uniNF (d₁ `, d₂) (.d₁ `, .d₂) = refl
  uniNF `unit      `unit        = refl
  uniNF (`nnf p)   (`nnf p′)    = `nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NNF d) → p ≡ p′
  uniNNF (`v i)     (`v .i)      = refl
  uniNNF (p₁ `$ p₂) (p₁′ `$ p₂′) = _`$_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (`proj₁ p) (`proj₁ p′)  = `proj₁ & uniNNF p p′
  uniNNF (`proj₂ p) (`proj₂ p′)  = `proj₂ & uniNNF p p′

mutual
  renNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NF d) → NF (ren e d)
  renNF e (`λ d)     = `λ (ren (keep e) d)
  renNF e (d₁ `, d₂) = ren e d₁ `, ren e d₂
  renNF e `unit      = `unit
  renNF e (`nnf p)   = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NNF d) → NNF (ren e d)
  renNNF e (`v i)     = `v (ren∋ e i)
  renNNF e (p₁ `$ p₂) = renNNF e p₁ `$ renNF e p₂
  renNNF e (`proj₁ p) = `proj₁ (renNNF e p)
  renNNF e (`proj₂ p) = `proj₂ (renNNF e p)


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  refl≝     : ∀ {A} {d : Γ ⊢ A} → d ≝ d
  sym≝      : ∀ {A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → d′ ≝ d
  trans≝    : ∀ {A} {d d′ d″ : Γ ⊢ A} (eq : d ≝ d′) (eq′ : d′ ≝ d″) → d ≝ d″
  cong$     : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) →
              d₁ `$ d₂ ≝ d₁′ `$ d₂′
  congproj₁ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (eq : d ≝ d′) → `proj₁ d ≝ `proj₁ d′
  congproj₂ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (eq : d ≝ d′) → `proj₂ d ≝ `proj₂ d′
  βred⊃     : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′) →
              `λ d₁ `$ d₂ ≝ d′
  βred∧₁    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₁ (d₁ `, d₂) ≝ d₁
  βred∧₂    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₂ (d₁ `, d₂) ≝ d₂

open ≝Kit (λ {_} {_} {d} → refl≝ {d = d}) sym≝ trans≝ public

-- call-by-value reduction
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  cong$₁    : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (r₁ : d₁ ⟹ d₁′) →
              d₁ `$ d₂ ⟹ d₁′ `$ d₂
  cong$₂    : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : NF d₁) (r₂ : d₂ ⟹ d₂′) →
              d₁ `$ d₂ ⟹ d₁ `$ d₂′
  congproj₁ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (r : d ⟹ d′) → `proj₁ d ⟹ `proj₁ d′
  congproj₂ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (r : d ⟹ d′) → `proj₂ d ⟹ `proj₂ d′
  βred⊃     : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′)
                (p₂ : NF d₂) →
              `λ d₁ `$ d₂ ⟹ d′
  βred∧₁    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₁ (d₁ `, d₂) ⟹ d₁
  βred∧₂    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₂ (d₁ `, d₂) ⟹ d₂

open ⟹Kit _⟹_ public

mutual
  NF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬R d
  NF→¬R (`nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {d  : Γ ⊢ A} (p : NNF d) → ¬R d
  NNF→¬R (p₁ `$ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ `$ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂
  NNF→¬R (`proj₁ p) (congproj₁ r)   = r ↯ NNF→¬R p
  NNF→¬R (`proj₂ p) (congproj₂ r)   = r ↯ NNF→¬R p

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) → d′ ≡ d″
det⟹ (cong$₁ r₁)     (cong$₁ r₁′)     = (_`$ _) & det⟹ r₁ r₁′
det⟹ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⟹ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⟹ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ `$_) & det⟹ r₂ r₂′
det⟹ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⟹ (congproj₁ r)   (congproj₁ r′)   = `proj₁ & det⟹ r r′
det⟹ (congproj₂ r)   (congproj₂ r′)   = `proj₂ & det⟹ r r′
det⟹ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⟹ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl
det⟹ βred∧₁          βred∧₁           = refl
det⟹ βred∧₂          βred∧₂           = refl

-- _⟹_ has unique proofs
uni⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (r r′ : d ⟹ d′) → r ≡ r′
uni⟹ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⟹ r₁ r₁′
uni⟹ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⟹ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⟹ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⟹ r₂ r₂′
uni⟹ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⟹ (congproj₁ r)   (congproj₁ r′)   = congproj₁ & uni⟹ r r′
uni⟹ (congproj₂ r)   (congproj₂ r′)   = congproj₂ & uni⟹ r r′
uni⟹ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⟹ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′
uni⟹ βred∧₁          βred∧₁           = refl
uni⟹ βred∧₂          βred∧₂           = refl

RF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → RF d ⊎ NF d
RF⊎NF (`v i)                        = nf (`nnf (`v i))
RF⊎NF (`λ d)                        = nf (`λ d)
RF⊎NF (d₁ `$ d₂)                    with RF⊎NF d₁ | RF⊎NF d₂
... | rf (d₁′ , r₁) | _               = rf (d₁′ `$ d₂ , cong$₁ r₁)
... | nf p₁         | rf (d₂′ , r₂)   = rf (d₁ `$ d₂′ , cong$₂ p₁ r₂)
... | nf (`λ d₁′)   | nf p₂           = rf (d₁′ [ d₂ ] , βred⊃ refl p₂)
... | nf (`nnf p₁)  | nf p₂           = nf (`nnf (p₁ `$ p₂))
RF⊎NF (d₁ `, d₂)                      = nf (d₁ `, d₂)
RF⊎NF (`proj₁ d)                    with RF⊎NF d
... | rf (d′ , r)                     = rf (`proj₁ d′ , congproj₁ r)
... | nf (d₁ `, d₂)                   = rf (d₁ , βred∧₁)
... | nf (`nnf p)                     = nf (`nnf (`proj₁ p))
RF⊎NF (`proj₂ d)                    with RF⊎NF d
... | rf (d′ , r)                     = rf (`proj₂ d′ , congproj₂ r)
... | nf (d₁ `, d₂)                   = rf (d₂ , βred∧₂)
... | nf (`nnf p)                   = nf (`nnf (`proj₂ p))
RF⊎NF `unit                         = nf `unit

open RF⊎NFKit NF→¬R RF⊎NF public

open ⟹*Kit det⟹ public


----------------------------------------------------------------------------------------------------
