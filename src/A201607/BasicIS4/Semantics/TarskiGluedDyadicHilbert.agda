{-# OPTIONS --sized-types #-}

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
-- Hilbert-style syntax.

module A201607.BasicIS4.Semantics.TarskiGluedDyadicHilbert where

open import A201607.BasicIS4.Syntax.Common public
open import A201607.Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_ _⁏_[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P

    -- Hilbert-style syntax representation; monotonic.
    _⁏_[⊢]_ : Cx Ty → Cx Ty → Ty → Set
    mono[⊢] : ∀ {A Γ Γ′ Δ}  → Γ ⊆ Γ′ → Γ ⁏ Δ [⊢] A → Γ′ ⁏ Δ [⊢] A
    [var]    : ∀ {A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [app]    : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [ci]     : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] A ▻ A
    [ck]     : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B ▻ A
    [cs]     : ∀ {A B C Γ Δ} → Γ ⁏ Δ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    [mvar]   : ∀ {A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]    : ∀ {A Γ Δ}     → ∅ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [cdist]  : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
    [cup]    : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] □ A ▻ □ □ A
    [cdown]  : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] □ A ▻ A
    [cpair]  : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B ▻ A ∧ B
    [cfst]   : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ∧ B ▻ A
    [csnd]   : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ∧ B ▻ B
    [unit]   : ∀ {Γ Δ}       → Γ ⁏ Δ [⊢] ⊤

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_
  _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⁏ Δ ⊩ α P   = Γ ⁏ Δ ⊩ᵅ P
  Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Glue (Γ′ ⁏ Δ [⊢] □ A) (Γ′ ⁏ Δ ⊩ A)
  Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ ⊤    = 𝟙

  infix 3 _⁏_⊩⋆_
  _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ ⊩⋆ ∅     = 𝟙
  Γ ⁏ Δ ⊩⋆ Ξ , A = Γ ⁏ Δ ⊩⋆ Ξ × Γ ⁏ Δ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
  mono⊩ {α P}   ψ s = mono⊩ᵅ ψ s
  mono⊩ {A ▻ B} ψ s = λ ψ′ → s (trans⊆ ψ ψ′)
  mono⊩ {□ A}   ψ s = λ ψ′ → s (trans⊆ ψ ψ′)
  mono⊩ {A ∧ B} ψ s = mono⊩ {A} ψ (π₁ s) , mono⊩ {B} ψ (π₂ s)
  mono⊩ {⊤}    ψ s = ∙

  mono⊩⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Ξ → Γ′ ⁏ Δ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ψ ∙        = ∙
  mono⊩⋆ {Ξ , A} ψ (ts , t) = mono⊩⋆ {Ξ} ψ ts , mono⊩ {A} ψ t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
  s ⟪$⟫ a = s refl⊆ a

  ⟪K⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A
  ⟪K⟫ {A} a ψ = K (mono⊩ {A} ψ a)

  ⟪S⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ C
  ⟪S⟫ {A} {B} {C} s₁ s₂ a = _⟪$⟫_ {B} {C} (_⟪$⟫_ {A} {B ▻ C} s₁ a) (_⟪$⟫_ {A} {B} s₂ a)

  ⟪S⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ψ s₂ ψ′ a = let s₁′ = mono⊩ {A ▻ B ▻ C} (trans⊆ ψ ψ′) s₁
                                      s₂′ = mono⊩ {A ▻ B} ψ′ s₂
                                  in  ⟪S⟫ {A} {B} {C} s₁′ s₂′ a

  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ ψ = let t ⅋ s₁′ = s₁ ψ
                              u ⅋ a   = s₂ ψ
                          in  [app] ([app] [cdist] t) u ⅋ (_⟪$⟫_ {A} {B} s₁′ a)

  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = _⟪D⟫_ (mono⊩ {□ (A ▻ B)} ψ s₁)

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ s ψ = [app] [cup] (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆ ψ ψ′)

  ⟪↓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
  ⟪↓⟫ s = sem (s refl⊆)

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a ψ = _,_ (mono⊩ {A} ψ a)


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_⇒_
  _⁏_⊩_⇒_ : Cx Ty → Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⁏ Δ ⊩ Γ ⇒ A = Γ₀ ⁏ Δ ⊩⋆ Γ → Γ₀ ⁏ Δ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ ⊩ A

  infix 3 _⁏_⊩_⇒⋆_
  _⁏_⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⁏ Δ ⊩ Γ ⇒⋆ Ξ = Γ₀ ⁏ Δ ⊩⋆ Γ → Γ₀ ⁏ Δ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ ⊩⋆ Ξ


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⁏_⊨_
_⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⇒ A

infix 3 _⁏_⊨⋆_
_⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
  mlookup top     (γ , s) = sem (s refl⊆)
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
