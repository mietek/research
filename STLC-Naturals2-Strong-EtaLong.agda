module STLC-Naturals2-Strong-EtaLong where

open import STLC-Naturals2 public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝    : ∀ {A B} {t : A ∷ Γ ⊢ B} (p : NF t) → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF (⌜c⌝ ⌜zero⌝)
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜c⌝ ⌜suc⌝ ⌜$⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} (pₙ : NNF tₙ) (p₀ : NF t₀)
              (p₁ : NF t₁) →
            NNF (⌜c⌝ ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ t₁)

-- renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e (⌜λ⌝ p)   = ⌜λ⌝ (renNF (keep e) p)
  renNF e ⌜zero⌝    = ⌜zero⌝
  renNF e (⌜suc⌝ p) = ⌜suc⌝ (renNF e p)
  renNF e (nnf p)   = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e ⌜v⌝-             = ⌜v⌝-
  renNNF e (p₁ ⌜$⌝ p₂)      = renNNF e p₁ ⌜$⌝ renNF e p₂
  renNNF e (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF e pₙ) (renNF e p₀) (renNF e pₛ)

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (⌜λ⌝ p)           (⌜λ⌝ p′)           = ⌜λ⌝ & uniNF p p′
  uniNF ⌜zero⌝            ⌜zero⌝             = refl
  uniNF (⌜suc⌝ p)         (⌜suc⌝ p′)         = ⌜suc⌝ & uniNF p p′
  uniNF (⌜suc⌝ p)         (nnf (() ⌜$⌝ p₂′))
  uniNF (nnf (() ⌜$⌝ p₂)) (⌜suc⌝ p′)
  uniNF (nnf p)           (nnf p′)           = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF ⌜v⌝-                        ⌜v⌝-                         = refl
  uniNNF (p₁ ⌜$⌝ p₂)                 (p₁′ ⌜$⌝ p₂′)                = _⌜$⌝_ & uniNNF p₁ p₁′
                                                                      ⊗ uniNF p₂ p₂′
  uniNNF (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂) (⌜rec⌝ pₙ′ p₀′ pₛ′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (⌜rec⌝ pₙ′ p₀′ pₛ′)          = ⌜rec⌝ & uniNNF pₙ pₙ′
                                                                      ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms (direct)
mutual
  infix 3 _⋘_
  data _⋘_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝    : ∀ {A B} (t : A ∷ Γ ⋘ B) → Γ ⋘ A ⌜⊃⌝ B
    ⌜zero⌝ : Γ ⋘ ⌜ℕ⌝
    ⌜suc⌝  : ∀ (t : Γ ⋘ ⌜ℕ⌝) → Γ ⋘ ⌜ℕ⌝
    nnf    : ∀ (t : Γ ⋙ ⌜ℕ⌝) → Γ ⋘ ⌜ℕ⌝

  -- neutrals
  infix 3 _⋙_
  data _⋙_ (Γ : Ctx) : Ty → Set where
    ⌜v⌝   : ∀ {A} (i : Γ ∋ A) → Γ ⋙ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⋙ A ⌜⊃⌝ B) (t₂ : Γ ⋘ A) → Γ ⋙ B
    ⌜rec⌝ : ∀ {A} (tₙ : Γ ⋙ ⌜ℕ⌝) (t₀ : Γ ⋘ A) (tₛ : Γ ⋘ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A)  → Γ ⋙ A

-- renaming
mutual
  ren⋘ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⋘ A → Γ′ ⋘ A
  ren⋘ e (⌜λ⌝ t)   = ⌜λ⌝ (ren⋘ (keep e) t)
  ren⋘ e ⌜zero⌝    = ⌜zero⌝
  ren⋘ e (⌜suc⌝ t) = ren⋘ e t
  ren⋘ e (nnf t)   = nnf (ren⋙ e t)

  ren⋙ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⋙ A → Γ′ ⋙ A
  ren⋙ e (⌜v⌝ i)          = ⌜v⌝ (ren∋ e i)
  ren⋙ e (t₁ ⌜$⌝ t₂)      = ren⋙ e t₁ ⌜$⌝ ren⋘ e t₂
  ren⋙ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren⋙ e tₙ) (ren⋘ e t₀) (ren⋘ e tₛ)


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  βredℕ₀ : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
           ⌜c⌝ ⌜rec⌝ ⌜$⌝ ⌜c⌝ ⌜zero⌝ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ t₀
  βredℕₛ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
           ⌜c⌝ ⌜rec⌝ ⌜$⌝ (⌜c⌝ ⌜suc⌝ ⌜$⌝ tₙ) ⌜$⌝ t₀ ⌜$⌝ tₛ ≝
             tₛ ⌜$⌝ tₙ ⌜$⌝ (⌜c⌝ ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ)
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------
