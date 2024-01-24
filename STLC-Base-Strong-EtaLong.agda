module STLC-Base-Strong-EtaLong where

open import STLC-Base public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms (predicate)
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `λ   : ∀ {A B} {t : A ∷ Γ ⊢ B} (p : NF t) → NF (`λ t)
    `nnf : ∀ {t : Γ ⊢ `◦} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `v   : ∀ {A} {i : Γ ∋ A} → NNF (`v i)
    _`$_ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ `$ t₂)

tmNF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → Γ ⊢ A
tmNF {t = t} p = t

tmNNF : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → Γ ⊢ A
tmNNF {t = t} p = t

-- renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e (`λ p)   = `λ (renNF (keep e) p)
  renNF e (`nnf p) = `nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e `v         = `v
  renNNF e (p₁ `$ p₂) = renNNF e p₁ `$ renNF e p₂

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (`λ p)   (`λ p′)   = `λ & uniNF p p′
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
  congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → `λ t ≝ `λ t′
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ `$ t₂ ≝ t₁′ `$ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           `λ t₁ `$ t₂ ≝ t′
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A `⊃ B} (eq : t′ ≡ `λ (weak t `$ `v zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------
