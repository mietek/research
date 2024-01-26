module STLC-Naturals2-Strong-EtaLong where

open import STLC-Naturals2 public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms
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
