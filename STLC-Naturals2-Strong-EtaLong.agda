module STLC-Naturals2-Strong-EtaLong where

open import STLC-Naturals2 public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms (intrinsic)
mutual
  infix 3 _⇇_
  data _⇇_ (Γ : Ctx) : Ty → Set where
    `zero : Γ ⇇ `ℕ
    `suc  : ∀ (t : Γ ⇇ `ℕ) → Γ ⇇ `ℕ
    `λ    : ∀ {A B} (t : A ∷ Γ ⇇ B) → Γ ⇇ A `⊃ B
    `nnf  : ∀ (t : Γ ⇉ `ℕ) → Γ ⇇ `ℕ

  -- neutrals
  infix 3 _⇉_
  data _⇉_ (Γ : Ctx) : Ty → Set where
    `rec : ∀ {A} (t₀ : Γ ⇇ A) (t₁ : Γ ⇇ `ℕ `⊃ A `⊃ A) (t : Γ ⇉ `ℕ) → Γ ⇉ A
    `v   : ∀ {A} (i : Γ ∋ A) → Γ ⇉ A
    _`$_ : ∀ {A B} (t₁ : Γ ⇉ A `⊃ B) (t₂ : Γ ⇇ A) → Γ ⇉ B

-- renaming
mutual
  ren⇇ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⇇ A → Γ′ ⇇ A
  ren⇇ e `zero    = `zero
  ren⇇ e (`suc t) = ren⇇ e t
  ren⇇ e (`λ t)   = `λ (ren⇇ (keep e) t)
  ren⇇ e (`nnf t) = `nnf (ren⇉ e t)

  ren⇉ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⇉ A → Γ′ ⇉ A
  ren⇉ e (`rec t₀ t₁ t) = `rec (ren⇇ e t₀) (ren⇇ e t₁) (ren⇉ e t)
  ren⇉ e (`v i)         = `v (ren∋ e i)
  ren⇉ e (t₁ `$ t₂)     = ren⇉ e t₁ `$ ren⇇ e t₂


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
  βredℕ₁ : ∀ {A} {t₀ : Γ ⊢ A} {t₁ : Γ ⊢ `ℕ `⊃ A `⊃ A} → `c `rec `$ t₀ `$ t₁ `$ `c `zero ≝ t₀
  βredℕ₂ : ∀ {A} {t₀ : Γ ⊢ A} {t₁ : Γ ⊢ `ℕ `⊃ A `⊃ A} {t : Γ ⊢ `ℕ} →
           `c `rec `$ t₀ `$ t₁ `$ (`c `suc `$ t) ≝ t₁ `$ t `$ (`c `rec `$ t₀ `$ t₁ `$ t)
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           `λ t₁ `$ t₂ ≝ t′
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A `⊃ B} (eq : t′ ≡ `λ (weak t `$ `v zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------
