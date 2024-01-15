module STLC-Naturals-Weak-NotEtaLong where

open import STLC-Naturals public


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short weak normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ    : ∀ {A B} (d : A ∷ Γ ⊢ B) → NF (`λ d)
    `zero : NF (`zero)
    `suc  : ∀ (d : Γ ⊢ `ℕ) → NF (`suc d)
    `nnf  : ∀ {A} {d : Γ ⊢ A} (p : NNF d) → NF d

  -- d is in neutral β-short weak normal form
  data NNF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `v   : ∀ {A} (i : Γ ∋ A) → NNF (`v i)
    _`$_ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (p₁ : NNF d₁) (p₂ : NF d₂) → NNF (d₁ `$ d₂)
    `rec : ∀ {A} {d₁ : Γ ⊢ `ℕ} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NNF d₁)
             (p₂ : NF d₂) (p₃ : NF d₃) →
           NNF (`rec d₁ d₂ d₃)

-- NF and NNF have unique proofs
mutual
  uniNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NF d) → p ≡ p′
  uniNF (`λ d)   (`λ .d)   = refl
  uniNF `zero    `zero     = refl
  uniNF (`suc d) (`suc .d) = refl
  uniNF (`nnf p) (`nnf p′) = `nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NNF d) → p ≡ p′
  uniNNF (`v i)          (`v .i)            = refl
  uniNNF (p₁ `$ p₂)      (p₁′ `$ p₂′)       = _`$_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (`rec p₁ p₂ p₃) (`rec p₁′ p₂′ p₃′) = `rec & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′

mutual
  renNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NF d) → NF (ren e d)
  renNF e (`λ d)   = `λ (ren (keep e) d)
  renNF e `zero    = `zero
  renNF e (`suc d) = `suc (ren e d)
  renNF e (`nnf p) = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NNF d) → NNF (ren e d)
  renNNF e (`v i)          = `v (ren∋ e i)
  renNNF e (p₁ `$ p₂)      = renNNF e p₁ `$ renNF e p₂
  renNNF e (`rec p₁ p₂ p₃) = `rec (renNNF e p₁) (renNF e p₂) (renNF (keep (keep e)) p₃)


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  refl≝   : ∀ {A} {d : Γ ⊢ A} → d ≝ d
  sym≝    : ∀ {A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → d′ ≝ d
  trans≝  : ∀ {A} {d d′ d″ : Γ ⊢ A} (eq : d ≝ d′) (eq′ : d′ ≝ d″) → d ≝ d″
  comp$   : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) →
            d₁ `$ d₂ ≝ d₁′ `$ d₂′
  comprec : ∀ {A} {d₁ d₁′ : Γ ⊢ `ℕ} {d₂ d₂′ : Γ ⊢ A} {d₃ d₃′ : A ∷ `ℕ ∷ Γ ⊢ A}
              (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) (eq₃ : d₃ ≝ d₃′) →
            `rec d₁ d₂ d₃ ≝ `rec d₁′ d₂′ d₃′
  βred⊃   : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′) →
            `λ d₁ `$ d₂ ≝ d′
  βredℕ₁  : ∀ {A} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} → `rec `zero d₂ d₃ ≝ d₂
  βredℕ₂  : ∀ {A} {d₁ : Γ ⊢ `ℕ} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} {d′ : Γ ⊢ A}
              (eq : d₃ [ d₁ ∣ `rec d₁ d₂ d₃ ] ≡ d′) →
            `rec (`suc d₁) d₂ d₃ ≝ d′

open ≝Kit (λ {_} {_} {d} → refl≝ {d = d}) sym≝ trans≝ public -- TODO: ugh

-- call-by-value conversion
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  comp$₁   : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (r₁ : d₁ ⟹ d₁′) →
             d₁ `$ d₂ ⟹ d₁′ `$ d₂
  comp$₂   : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : NF d₁) (r₂ : d₂ ⟹ d₂′) →
             d₁ `$ d₂ ⟹ d₁ `$ d₂′
  comprec₁ : ∀ {A} {d₁ d₁′ : Γ ⊢ `ℕ} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} (r₁ : d₁ ⟹ d₁′) →
             `rec d₁ d₂ d₃ ⟹ `rec d₁′ d₂ d₃
  comprec₂ : ∀ {A} {d₁ : Γ ⊢ `ℕ} {d₂ d₂′ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NF d₁)
               (r₂ : d₂ ⟹ d₂′) →
             `rec d₁ d₂ d₃ ⟹ `rec d₁ d₂′ d₃
  comprec₃ : ∀ {A} {d₁ : Γ ⊢ `ℕ} {d₂ : Γ ⊢ A} {d₃ d₃′ : A ∷ `ℕ ∷ Γ ⊢ A} (p₁ : NF d₁)
               (p₂ : NF d₂) (r₃ : d₃ ⟹ d₃′) →
             `rec d₁ d₂ d₃ ⟹ `rec d₁ d₂ d₃′
  βred⊃    : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′)
               (p₂ : NF d₂) →
             `λ d₁ `$ d₂ ⟹ d′
  βredℕ₁   : ∀ {A} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} (p₂ : NF d₂) (p₃ : NF d₃) →
             `rec `zero d₂ d₃ ⟹ d₂
  βredℕ₂   : ∀ {A} {d₁ : Γ ⊢ `ℕ} {d₂ : Γ ⊢ A} {d₃ : A ∷ `ℕ ∷ Γ ⊢ A} {d′ : Γ ⊢ A}
               (eq : d₃ [ d₁ ∣ `rec d₁ d₂ d₃ ] ≡ d′) (p₂ : NF d₂) (p₃ : NF d₃) →
             `rec (`suc d₁) d₂ d₃ ⟹ d′

open ⟹Kit _⟹_ public

mutual
  NF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬R d
  NF→¬R (`nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {d  : Γ ⊢ A} (p : NNF d) → ¬R d
  NNF→¬R (p₁ `$ p₂)      (comp$₁ r₁)           = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ `$ p₂)      (comp$₂ p₁′ r₂)       = r₂ ↯ NF→¬R p₂
  NNF→¬R (() `$ p₂)      (βred⊃ eq p₂′)
  NNF→¬R (`rec p₁ p₂ p₃) (comprec₁ r₁)         = r₁ ↯ NNF→¬R p₁
  NNF→¬R (`rec p₁ p₂ p₃) (comprec₂ p₁′ r₂)     = r₂ ↯ NF→¬R p₂
  NNF→¬R (`rec p₁ p₂ p₃) (comprec₃ p₁′ p₂′ r₃) = r₃ ↯ NF→¬R p₃

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) → d′ ≡ d″
det⟹ (comp$₁ r₁)         (comp$₁ r₁′)           = (_`$ _) & det⟹ r₁ r₁′
det⟹ (comp$₁ r₁)         (comp$₂ p₁′ r₂′)       = r₁ ↯ NF→¬R p₁′
det⟹ (comp$₂ p₁ r₂)      (comp$₁ r₁′)           = r₁′ ↯ NF→¬R p₁
det⟹ (comp$₂ p₁ r₂)      (comp$₂ p₁′ r₂′)       = (_ `$_) & det⟹ r₂ r₂′
det⟹ (comp$₂ p₁ r₂)      (βred⊃ refl p₂′)       = r₂ ↯ NF→¬R p₂′
det⟹ (comprec₁ r₁)       (comprec₁ r₁′)         = _ & det⟹ r₁ r₁′
det⟹ (comprec₁ r₁)       (comprec₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
det⟹ (comprec₁ r₁)       (comprec₃ p₁′ p₂′ r₃′) = r₁ ↯ NF→¬R p₁′
det⟹ (comprec₂ p₁ r₂)    (comprec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
det⟹ (comprec₂ p₁ r₂)    (comprec₂ p₁′ r₂′)     = _ & uniNF p₁ p₁′ ⊗ det⟹ r₂ r₂′
det⟹ (comprec₂ p₁ r₂)    (comprec₃ p₁′ p₂′ r₃′) = r₂ ↯ NF→¬R p₂′
det⟹ (comprec₂ p₁ r₂)    (βredℕ₁ p₂′ p₃′)       = r₂ ↯ NF→¬R p₂′
det⟹ (comprec₂ p₁ r₂)    (βredℕ₂ refl p₂′ p₃′)  = r₂ ↯ NF→¬R p₂′
det⟹ (comprec₃ p₁ p₂ r₃) (comprec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
det⟹ (comprec₃ p₁ p₂ r₃) (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⟹ (comprec₃ p₁ p₂ r₃) (comprec₃ p₁′ p₂′ r₃′) = _ & uniNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗
                                                      det⟹ r₃ r₃′
det⟹ (comprec₃ p₁ p₂ r₃) (βredℕ₁ p₂′ p₃′)       = r₃ ↯ NF→¬R p₃′
det⟹ (comprec₃ p₁ p₂ r₃) (βredℕ₂ refl p₂′ p₃′)  = r₃ ↯ NF→¬R p₃′
det⟹ (βred⊃ refl p₂)     (comp$₂ p₁′ r₂′)       = r₂′ ↯ NF→¬R p₂
det⟹ (βred⊃ refl p₂)     (βred⊃ refl p₂′)       = refl
det⟹ (βredℕ₁ p₂ p₃)      (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⟹ (βredℕ₁ p₂ p₃)      (comprec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
det⟹ (βredℕ₁ p₂ p₃)      (βredℕ₁ p₂′ p₃′)       = refl
det⟹ (βredℕ₂ refl p₂ p₃) (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⟹ (βredℕ₂ refl p₂ p₃) (comprec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
det⟹ (βredℕ₂ refl p₂ p₃) (βredℕ₂ refl p₂′ p₃′)  = refl

-- _⟹_ has unique proofs
uni⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (r r′ : d ⟹ d′) → r ≡ r′
uni⟹ (comp$₁ r₁)         (comp$₁ r₁′)           = comp$₁ & uni⟹ r₁ r₁′
uni⟹ (comp$₁ r₁)         (comp$₂ p₁′ r₂′)       = r₁ ↯ NF→¬R p₁′
uni⟹ (comp$₂ p₁ r₂)      (comp$₁ r₁′)           = r₁′ ↯ NF→¬R p₁
uni⟹ (comp$₂ p₁ r₂)      (comp$₂ p₁′ r₂′)       = comp$₂ & uniNF p₁ p₁′ ⊗ uni⟹ r₂ r₂′
uni⟹ (comp$₂ p₁ r₂)      (βred⊃ eq′ p₂)         = r₂ ↯ NF→¬R p₂
uni⟹ (comprec₁ r₁)       (comprec₁ r₁′)         = comprec₁ & uni⟹ r₁ r₁′
uni⟹ (comprec₁ r₁)       (comprec₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
uni⟹ (comprec₁ r₁)       (comprec₃ p₁′ p₂′ r₃′) = r₁ ↯ NF→¬R p₁′
uni⟹ (comprec₂ p₁ r₂)    (comprec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
uni⟹ (comprec₂ p₁ r₂)    (comprec₂ p₁′ r₂′)     = comprec₂ & uniNF p₁ p₁′ ⊗ uni⟹ r₂ r₂′
uni⟹ (comprec₂ p₁ r₂)    (comprec₃ p₁′ p₂′ r₃′) = r₂ ↯ NF→¬R p₂′
uni⟹ (comprec₂ p₁ r₂)    (βredℕ₁ p₂′ p₃′)       = r₂ ↯ NF→¬R p₂′
uni⟹ (comprec₂ p₁ r₂)    (βredℕ₂ eq′ p₂′ p₃′)   = r₂ ↯ NF→¬R p₂′
uni⟹ (comprec₃ p₁ p₂ r₃) (comprec₁ r₁′)         = r₁′ ↯ NF→¬R p₁
uni⟹ (comprec₃ p₁ p₂ r₃) (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⟹ (comprec₃ p₁ p₂ r₃) (comprec₃ p₁′ p₂′ r₃′) = comprec₃ & uniNF p₁ p₁′ ⊗ uniNF p₂ p₂′ ⊗
                                                      uni⟹ r₃ r₃′
uni⟹ (comprec₃ p₁ p₂ r₃) (βredℕ₂ eq′ p₂′ p₃′)   = r₃ ↯ NF→¬R p₃′
uni⟹ (βred⊃ eq p₂)       (comp$₂ p₁′ r₂′)       = r₂′ ↯ NF→¬R p₂
uni⟹ (βred⊃ refl p₂)     (βred⊃ refl p₂′)       = βred⊃ refl & uniNF p₂ p₂′
uni⟹ (βredℕ₁ p₂ p₃)      (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⟹ (βredℕ₁ p₂ p₃)      (βredℕ₁ p₂′ p₃′)       = βredℕ₁ & uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′
uni⟹ (βredℕ₂ eq p₂ p₃)   (comprec₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⟹ (βredℕ₂ eq p₂ p₃)   (comprec₃ p₁′ p₂′ r₃′) = r₃′ ↯ NF→¬R p₃
uni⟹ (βredℕ₂ refl p₂ p₃) (βredℕ₂ refl p₂′ p₃′)  = βredℕ₂ refl & uniNF p₂ p₂′ ⊗ uniNF p₃ p₃′

RF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → RF d ⊎ NF d
RF⊎NF (`v i)                                        = nf (`nnf (`v i))
RF⊎NF (`λ d)                                        = nf (`λ d)
RF⊎NF (d₁ `$ d₂)                                    with RF⊎NF d₁ | RF⊎NF d₂
... | rf (d₁′ , r₁) | _                               = rf (d₁′ `$ d₂ , comp$₁ r₁)
... | nf p₁         | rf (d₂′ , r₂)                   = rf (d₁ `$ d₂′ , comp$₂ p₁ r₂)
... | nf (`λ d₁′)   | nf p₂                           = rf (d₁′ [ d₂ ] , βred⊃ refl p₂)
... | nf (`nnf p₁)  | nf p₂                           = nf (`nnf (p₁ `$ p₂))
RF⊎NF `zero                                         = nf `zero
RF⊎NF (`suc d)                                      = nf (`suc d)
RF⊎NF (`rec d₁ d₂ d₃)                               with RF⊎NF d₁ | RF⊎NF d₂ | RF⊎NF d₃
... | rf (d₁′ , r₁) | _             | _               = rf (`rec d₁′ d₂ d₃ , comprec₁ r₁)
... | nf p₁         | rf (d₂′ , r₂) | _               = rf (`rec d₁ d₂′ d₃ , comprec₂ p₁ r₂)
... | nf p₁         | nf p₂         | rf (d₃′ , r₃)   = rf (`rec d₁ d₂ d₃′ , comprec₃ p₁ p₂ r₃)
... | nf `zero      | nf p₂         | nf p₃           = rf (d₂ , βredℕ₁ p₂ p₃)
... | nf (`suc d₁′) | nf p₂         | nf p₃           = rf (d₃ [ d₁′ ∣ `rec d₁′ d₂ d₃ ] ,
                                                          βredℕ₂ refl p₂ p₃)
... | nf (`nnf p₁)  | nf p₂         | nf p₃           = nf (`nnf (`rec p₁ p₂ p₃))

open RF⊎NFKit NF→¬R RF⊎NF public

open ⟹*Kit det⟹ public


----------------------------------------------------------------------------------------------------
