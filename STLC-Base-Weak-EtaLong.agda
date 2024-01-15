module STLC-Base-Weak-EtaLong where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short η-long weak normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ   : ∀ {A B} (d : A ∷ Γ ⊢ B) → NF (`λ d)
    `nnf : ∀ {d : Γ ⊢ `◦} (p : NNF d) → NF d

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
  cong$  : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (eq₁ : d₁ ≝ d₁′) (eq₂ : d₂ ≝ d₂′) →
           d₁ `$ d₂ ≝ d₁′ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′) →
           `λ d₁ `$ d₂ ≝ d′
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) →
           d ≝ `λ (d′ `$ `v zero)

open ≝Kit (λ {_} {_} {d} → refl≝ {d = d}) sym≝ trans≝ public

-- call-by-value reduction
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  cong$₁ : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (q₁ : NAF d₁) (r₁ : d₁ ⟹ d₁′) →
           d₁ `$ d₂ ⟹ d₁′ `$ d₂
  cong$₂ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : NF d₁) (r₂ : d₂ ⟹ d₂′) →
           d₁ `$ d₂ ⟹ d₁ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : d₁ [ d₂ ] ≡ d′)
             (p₂ : NF d₂) →
           `λ d₁ `$ d₂ ⟹ d′
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) (p : NF d)
             (q : NAF d) →
           d ⟹ `λ (d′ `$ `v zero)

open ⟹Kit _⟹_ public

mutual
  NF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬R d
  NF→¬R (`λ d)   (ηexp⊃ refl p ())
  NF→¬R (`nnf p) r                 = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {d  : Γ ⊢ A} (p : NNF d) → ¬R d
  NNF→¬R (`v i)     (ηexp⊃ refl () q)
  NNF→¬R (p₁ `$ p₂) (cong$₁ q₁ r₁)    = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ `$ p₂) (cong$₂ p₁′ r₂)   = r₂ ↯ NF→¬R p₂
  NNF→¬R (() `$ p₂) (βred⊃ refl p₂′)
  NNF→¬R (p₁ `$ p₂) (ηexp⊃ refl () q)

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) → d′ ≡ d″
det⟹ (cong$₁ q₁ r₁)   (cong$₁ q₁′ r₁′)   = (_`$ _) & det⟹ r₁ r₁′
det⟹ (cong$₁ q₁ r₁)   (cong$₂ p₁′ r₂′)   = r₁ ↯ NF→¬R p₁′
det⟹ (cong$₁ () r₁)   (βred⊃ refl p₂′)
det⟹ (cong$₂ p₁ r₂)   (cong$₁ q₁′ r₁′)   = r₁′ ↯ NF→¬R p₁
det⟹ (cong$₂ p₁ r₂)   (cong$₂ p₁′ r₂′)   = (_ `$_) & det⟹ r₂ r₂′
det⟹ (cong$₂ p₁ r₂)   (βred⊃ refl p₂′)   = r₂ ↯ NF→¬R p₂′
det⟹ (βred⊃ refl p₂)  (cong$₂ p₁′ r₂′)   = r₂′ ↯ NF→¬R p₂
det⟹ (βred⊃ refl p₂)  (βred⊃ refl p₂′)   = refl
det⟹ (βred⊃ refl p₂)  (cong$₁ () r₁′)
det⟹ (ηexp⊃ refl p q) (ηexp⊃ refl p′ q′) = refl

-- _⟹_ has unique proofs
uni⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (r r′ : d ⟹ d′) → r ≡ r′
uni⟹ (cong$₁ q₁ r₁)   (cong$₁ q₁′ r₁′)   = cong$₁ & uniNAF q₁ q₁′ ⊗ uni⟹ r₁ r₁′
uni⟹ (cong$₁ q₁ r₁)   (cong$₂ p₁′ r₂′)   = r₁ ↯ NF→¬R p₁′
uni⟹ (cong$₂ p₁ r₂)   (cong$₁ q₁′ r₁′)   = r₁′ ↯ NF→¬R p₁
uni⟹ (cong$₂ p₁ r₂)   (cong$₂ p₁′ r₂′)   = cong$₂ & uniNF p₁ p₁′ ⊗ uni⟹ r₂ r₂′
uni⟹ (cong$₂ p₁ r₂)   (βred⊃ eq′ p₂′)    = r₂ ↯ NF→¬R p₂′
uni⟹ (βred⊃ eq p₂)    (cong$₂ p₁′ r₂′)   = r₂′ ↯ NF→¬R p₂
uni⟹ (βred⊃ refl p₂)  (βred⊃ refl p₂′)   = βred⊃ refl & uniNF p₂ p₂′
uni⟹ (ηexp⊃ refl p q) (ηexp⊃ refl p′ q′) = ηexp⊃ refl & uniNF p p′ ⊗ uniNAF q q′

-- -- TODO: what to do about η-expansion?
-- RF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → RF d ⊎ NF d
-- RF⊎NF {A = `◦}     (`v i)           = nf (`nnf (`v i))
-- RF⊎NF {A = A `⊃ B} (`v i)           = rf (`λ (weak (`v i) `$ `v zero) , ηexp⊃ refl {!!} (`v i))
-- RF⊎NF              (`λ d)           = nf (`λ d)
-- RF⊎NF              (d₁ `$ d₂)       with RF⊎NF d₁ | RF⊎NF d₂
-- ... | rf (d₁′ , r₁) | _               = rf (d₁′ `$ d₂ , cong$₁ {!!} r₁)
-- ... | nf p₁         | rf (d₂′ , r₂)   = rf (d₁ `$ d₂′ , cong$₂ p₁ r₂)
-- ... | nf (`λ d₁′)   | nf p₂           = rf (d₁′ [ d₂ ] , βred⊃ refl p₂)
--
-- open RF⊎NFKit NF→¬R RF⊎NF public
--
-- open ⟹*Kit det⟹ public


----------------------------------------------------------------------------------------------------
