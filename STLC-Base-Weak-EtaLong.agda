module STLC-Base-Weak-EtaLong where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short η-long weak normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ   : ∀ {A B} (d : A ∷ Γ ⊢ B) → NF (`λ d)
    `nnf : ∀ {d : Γ ⊢ `∙} (p : NNF d) → NF d

  -- d is in neutral β-short η-long weak normal form
  data NNF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `v   : ∀ {A} (i : Γ ∋ A) → NNF (`v i)
    _`$_ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (p₁ : NNF d₁) (p₂ : NF d₂) → NNF (d₁ `$ d₂)

-- d is in non-abstraction form (not `λ)
data NAF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
  `v   : ∀ {A} (i : Γ ∋ A) → NAF (`v i)
  _`$_ : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → NAF (d₁ `$ d₂)

-- NF and NNF have unique proofs
mutual
  uniNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NF d) → p ≡ p′
  uniNF (`λ d)   (`λ .d)   = refl
  uniNF (`nnf p) (`nnf p′) = `nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NNF d) → p ≡ p′
  uniNNF (`v i)     (`v .i)      = refl
  uniNNF (p₁ `$ p₂) (p₁′ `$ p₂′) = _`$_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′

-- NAF has unique proofs
uniNAF : ∀ {Γ A} {d : Γ ⊢ A} (p p′ : NAF d) → p ≡ p′
uniNAF (`v i)     (`v .i)      = refl
uniNAF (d₁ `$ d₂) (.d₁ `$ .d₂) = refl

mutual
  renNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NF d) → NF (ren e d)
  renNF e (`λ d)   = `λ (ren (keep e) d)
  renNF e (`nnf p) = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (p : NNF d) → NNF (ren e d)
  renNNF e (`v i)     = `v (ren∋ e i)
  renNNF e (p₁ `$ p₂) = renNNF e p₁ `$ renNF e p₂


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  refl≝  : ∀ {A} {d : Γ ⊢ A} → d ≝ d
  sym≝   : ∀ {A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → d′ ≝ d
  trans≝ : ∀ {A} {d d′ d″ : Γ ⊢ A} (eq : d ≝ d′) (eq′ : d′ ≝ d″) → d ≝ d″
  comp$  : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) →
           d₁ `$ d₂ ≝ d₁′ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′) →
           `λ d₁ `$ d₂ ≝ d′
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) →
           d ≝ `λ (d′ `$ `v zero)

open ≝Kit (λ {_} {_} {d} → refl≝ {d = d}) sym≝ trans≝ public -- TODO: ugh

-- call-by-value conversion
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  comp$₁ : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (q₁ : NAF d₁) (c₁ : d₁ ⟹ d₁′) →
           d₁ `$ d₂ ⟹ d₁′ `$ d₂
  comp$₂ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : NF d₁) (c₂ : d₂ ⟹ d₂′) →
           d₁ `$ d₂ ⟹ d₁ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′)
             (p₂ : NF d₂) →
           `λ d₁ `$ d₂ ⟹ d′
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) (p : NF d)
             (q : NAF d) →
           d ⟹ `λ (d′ `$ `v zero)

open ⟹Kit _⟹_ public

mutual
  NF→¬C : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬C d
  NF→¬C (`λ d)   (ηexp⊃ refl p ())
  NF→¬C (`nnf p) c                 = c ↯ NNF→¬C p

  NNF→¬C : ∀ {Γ A} {d  : Γ ⊢ A} (p : NNF d) → ¬C d
  NNF→¬C (`v i)     (ηexp⊃ refl () q)
  NNF→¬C (p₁ `$ p₂) (comp$₁ q₁ c₁)    = c₁ ↯ NNF→¬C p₁
  NNF→¬C (p₁ `$ p₂) (comp$₂ p₁′ c₂)   = c₂ ↯ NF→¬C p₂
  NNF→¬C (() `$ p₂) (βred⊃ refl p₂′)
  NNF→¬C (p₁ `$ p₂) (ηexp⊃ refl () q)

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (c : d ⟹ d′) (c′ : d ⟹ d″) → d′ ≡ d″
det⟹ (comp$₁ q₁ c₁)   (comp$₁ q₁′ c₁′)   = (_`$ _) & det⟹ c₁ c₁′
det⟹ (comp$₁ q₁ c₁)   (comp$₂ p₁′ c₂′)   = c₁ ↯ NF→¬C p₁′
det⟹ (comp$₁ () c₁)   (βred⊃ refl p₂′)
det⟹ (comp$₂ p₁ c₂)   (comp$₁ q₁′ c₁′)   = c₁′ ↯ NF→¬C p₁
det⟹ (comp$₂ p₁ c₂)   (comp$₂ p₁′ c₂′)   = (_ `$_) & det⟹ c₂ c₂′
det⟹ (comp$₂ p₁ c₂)   (βred⊃ refl p₂′)   = c₂ ↯ NF→¬C p₂′
det⟹ (βred⊃ refl p₂)  (comp$₂ p₁′ c₂′)   = c₂′ ↯ NF→¬C p₂
det⟹ (βred⊃ refl p₂)  (βred⊃ refl p₂′)   = refl
det⟹ (βred⊃ refl p₂)  (comp$₁ () c₁′)
det⟹ (ηexp⊃ refl p q) (ηexp⊃ refl p′ q′) = refl

-- _⟹_ has unique proofs
uni⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (c c′ : d ⟹ d′) → c ≡ c′
uni⟹ (comp$₁ q₁ c₁)   (comp$₁ q₁′ c₁′)   = comp$₁ & uniNAF q₁ q₁′ ⊗ uni⟹ c₁ c₁′
uni⟹ (comp$₁ q₁ c₁)   (comp$₂ p₁′ c₂′)   = c₁ ↯ NF→¬C p₁′
uni⟹ (comp$₂ p₁ c₂)   (comp$₁ q₁′ c₁′)   = c₁′ ↯ NF→¬C p₁
uni⟹ (comp$₂ p₁ c₂)   (comp$₂ p₁′ c₂′)   = comp$₂ & uniNF p₁ p₁′ ⊗ uni⟹ c₂ c₂′
uni⟹ (comp$₂ p₁ c₂)   (βred⊃ eq′ p₂′)    = c₂ ↯ NF→¬C p₂′
uni⟹ (βred⊃ eq p₂)    (comp$₂ p₁′ c₂′)   = c₂′ ↯ NF→¬C p₂
uni⟹ (βred⊃ refl p₂)  (βred⊃ refl p₂′)   = βred⊃ refl & uniNF p₂ p₂′
uni⟹ (ηexp⊃ refl p q) (ηexp⊃ refl p′ q′) = ηexp⊃ refl & uniNF p p′ ⊗ uniNAF q q′

pattern cf p = inj₁ p
pattern nf p = inj₂ p

-- -- TODO: what to do about η-expansion?
-- CF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → CF d ⊎ NF d
-- CF⊎NF {A = `∙}     (`v i)           = nf (`nnf (`v i))
-- CF⊎NF {A = A `⊃ B} (`v i)           = cf (`λ (weak (`v i) `$ `v zero) , ηexp⊃ refl {!!} (`v i))
-- CF⊎NF              (`λ d)           = nf (`λ d)
-- CF⊎NF              (d₁ `$ d₂)       with CF⊎NF d₁ | CF⊎NF d₂
-- ... | cf (d₁′ , c₁) | _               = cf (d₁′ `$ d₂ , comp$₁ {!!} c₁)
-- ... | nf p₁         | cf (d₂′ , c₂)   = cf (d₁ `$ d₂′ , comp$₂ p₁ c₂)
-- ... | nf (`λ d₁′)   | nf p₂           = cf (d₁′ [ d₂ ] , βred⊃ refl p₂)

-- open CF⊎NFKit NF→¬C CF⊎NF public

-- open ⟹*Kit det⟹ public


-- ----------------------------------------------------------------------------------------------------
