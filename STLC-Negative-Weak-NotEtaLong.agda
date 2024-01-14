module STLC-Negative-Weak-NotEtaLong where

open import STLC-Negative public


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short weak normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ    : ∀ {A B} (d : A ∷ Γ ⊢ B) → NF (`λ d)
    _`,_  : ∀ {A B} (d₁ : Γ ⊢ A) (d₂ : Γ ⊢ B) → NF (d₁ `, d₂)
    `unit : NF `unit
    `nnf  : ∀ {A} {d : Γ ⊢ A} (p : NNF d) → NF d

  -- d is in β-short neutral weak normal form
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
  comp$     : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) →
              d₁ `$ d₂ ≝ d₁′ `$ d₂′
  compproj₁ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (eq : d ≝ d′) → `proj₁ d ≝ `proj₁ d′
  compproj₂ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (eq : d ≝ d′) → `proj₂ d ≝ `proj₂ d′
  βred⊃     : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′) →
              `λ d₁ `$ d₂ ≝ d′
  βred∧₁    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₁ (d₁ `, d₂) ≝ d₁
  βred∧₂    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₂ (d₁ `, d₂) ≝ d₂

open ≝Kit (λ {_} {_} {d} → refl≝ {d = d}) sym≝ trans≝ public -- TODO: ugh

-- call-by-value conversion
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  comp$₁    : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (c₁ : d₁ ⟹ d₁′) →
              d₁ `$ d₂ ⟹ d₁′ `$ d₂
  comp$₂    : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : NF d₁) (c₂ : d₂ ⟹ d₂′) →
              d₁ `$ d₂ ⟹ d₁ `$ d₂′
  compproj₁ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (c : d ⟹ d′) → `proj₁ d ⟹ `proj₁ d′
  compproj₂ : ∀ {A B} {d d′ : Γ ⊢ A `∧ B} (c : d ⟹ d′) → `proj₂ d ⟹ `proj₂ d′
  βred⊃     : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′)
                (p₂ : NF d₂) →
              `λ d₁ `$ d₂ ⟹ d′
  βred∧₁    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₁ (d₁ `, d₂) ⟹ d₁
  βred∧₂    : ∀ {A B} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ B} → `proj₂ (d₁ `, d₂) ⟹ d₂

open ⟹Kit _⟹_ public

mutual
  NF→¬C : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬C d
  NF→¬C (`nnf p) c = c ↯ NNF→¬C p

  NNF→¬C : ∀ {Γ A} {d  : Γ ⊢ A} (p : NNF d) → ¬C d
  NNF→¬C (p₁ `$ p₂) (comp$₁ c₁)     = c₁ ↯ NNF→¬C p₁
  NNF→¬C (p₁ `$ p₂) (comp$₂ p₁′ c₂) = c₂ ↯ NF→¬C p₂
  NNF→¬C (`proj₁ p) (compproj₁ c)   = c ↯ NNF→¬C p
  NNF→¬C (`proj₂ p) (compproj₂ c)   = c ↯ NNF→¬C p

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (c : d ⟹ d′) (c′ : d ⟹ d″) → d′ ≡ d″
det⟹ (comp$₁ c₁)     (comp$₁ c₁′)     = (_`$ _) & det⟹ c₁ c₁′
det⟹ (comp$₁ c₁)     (comp$₂ p₁′ c₂′) = c₁ ↯ NF→¬C p₁′
det⟹ (comp$₂ p₁ c₂)  (comp$₁ c₁′)     = c₁′ ↯ NF→¬C p₁
det⟹ (comp$₂ p₁ c₂)  (comp$₂ p₁′ c₂′) = (_ `$_) & det⟹ c₂ c₂′
det⟹ (comp$₂ p₁ c₂)  (βred⊃ refl p₂′) = c₂ ↯ NF→¬C p₂′
det⟹ (compproj₁ c)   (compproj₁ c′)   = `proj₁ & det⟹ c c′
det⟹ (compproj₂ c)   (compproj₂ c′)   = `proj₂ & det⟹ c c′
det⟹ (βred⊃ refl p₂) (comp$₂ p₁′ c₂′) = c₂′ ↯ NF→¬C p₂
det⟹ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl
det⟹ βred∧₁          βred∧₁           = refl
det⟹ βred∧₂          βred∧₂           = refl

-- _⟹_ has unique proofs
uni⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (c c′ : d ⟹ d′) → c ≡ c′
uni⟹ (comp$₁ c₁)     (comp$₁ c₁′)     = comp$₁ & uni⟹ c₁ c₁′
uni⟹ (comp$₁ c₁)     (comp$₂ p₁′ c₂′) = c₁ ↯ NF→¬C p₁′
uni⟹ (comp$₂ p₁ c₂)  (comp$₁ c₁′)     = c₁′ ↯ NF→¬C p₁
uni⟹ (comp$₂ p₁ c₂)  (comp$₂ p₁′ c₂′) = comp$₂ & uniNF p₁ p₁′ ⊗ uni⟹ c₂ c₂′
uni⟹ (comp$₂ p₁ c₂)  (βred⊃ eq′ p₂′)  = c₂ ↯ NF→¬C p₂′
uni⟹ (compproj₁ c)   (compproj₁ c′)   = compproj₁ & uni⟹ c c′
uni⟹ (compproj₂ c)   (compproj₂ c′)   = compproj₂ & uni⟹ c c′
uni⟹ (βred⊃ eq p₂)   (comp$₂ p₁′ c₂′) = c₂′ ↯ NF→¬C p₂
uni⟹ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′
uni⟹ βred∧₁          βred∧₁           = refl
uni⟹ βred∧₂          βred∧₂           = refl

pattern cf p = inj₁ p
pattern nf p = inj₂ p

CF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → CF d ⊎ NF d
CF⊎NF (`v i)                        = nf (`nnf (`v i))
CF⊎NF (`λ d)                        = nf (`λ d)
CF⊎NF (d₁ `$ d₂)                    with CF⊎NF d₁ | CF⊎NF d₂
... | cf (d₁′ , c₁) | _               = cf (d₁′ `$ d₂ , comp$₁ c₁)
... | nf p₁         | cf (d₂′ , c₂)   = cf (d₁ `$ d₂′ , comp$₂ p₁ c₂)
... | nf (`λ d₁′)   | nf p₂           = cf (d₁′ [ d₂ ] , βred⊃ refl p₂)
... | nf (`nnf p₁)  | nf p₂           = nf (`nnf (p₁ `$ p₂))
CF⊎NF (d₁ `, d₂)                      = nf (d₁ `, d₂)
CF⊎NF (`proj₁ d)                    with CF⊎NF d
... | cf (d′ , c)                     = cf (`proj₁ d′ , compproj₁ c)
... | nf (d₁ `, d₂)                   = cf (d₁ , βred∧₁)
... | nf (`nnf p)                     = nf (`nnf (`proj₁ p))
CF⊎NF (`proj₂ d)                    with CF⊎NF d
... | cf (d′ , c)                     = cf (`proj₂ d′ , compproj₂ c)
... | nf (d₁ `, d₂)                   = cf (d₂ , βred∧₂)
... | nf (`nnf p)                   = nf (`nnf (`proj₂ p))
CF⊎NF `unit                         = nf `unit

open CF⊎NFKit NF→¬C CF⊎NF public

open ⟹*Kit det⟹ public


----------------------------------------------------------------------------------------------------
