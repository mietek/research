-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
-- Implicit syntax.

module BasicIS4.Semantics.TarskiGluedDyadicImplicit where

open import BasicIS4.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_ : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P

open Model {{…}} public




module ImplicitSyntax
    (_⁏_[⊢]_ : Cx Ty → Cx Ty → Ty → Set)
  where


  -- Forcing in a particular model.

  module _ {{_ : Model}} where
    infix 3 _⁏_⊩_
    _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
    Γ ⁏ Δ ⊩ α P   = Γ ⁏ Δ ⊩ᵅ P
    Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ B
    Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Glue (Γ′ ⁏ Δ [⊢] (□ A)) (Γ′ ⁏ Δ ⊩ A)
    Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
    Γ ⁏ Δ ⊩ ⊤    = 𝟙

    infix 3 _⁏_⊩⋆_
    _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
    Γ ⁏ Δ ⊩⋆ ⌀     = 𝟙
    Γ ⁏ Δ ⊩⋆ Ξ , A = Γ ⁏ Δ ⊩⋆ Ξ × Γ ⁏ Δ ⊩ A


  -- Monotonicity with respect to context inclusion.

  module _ {{_ : Model}} where
    mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
    mono⊩ {α P}   η s = mono⊩ᵅ η s
    mono⊩ {A ▻ B} η s = λ η′ → s (trans⊆ η η′)
    mono⊩ {□ A}   η s = λ η′ → s (trans⊆ η η′)
    mono⊩ {A ∧ B} η s = mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s)
    mono⊩ {⊤}    η s = ∙

    mono⊩⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Ξ → Γ′ ⁏ Δ ⊩⋆ Ξ
    mono⊩⋆ {⌀}     η ∙        = ∙
    mono⊩⋆ {Ξ , A} η (ts , t) = mono⊩⋆ {Ξ} η ts , mono⊩ {A} η t


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
    s ⟪$⟫ a = s refl⊆ a

    ⟪K⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A
    ⟪K⟫ {A} a η = K (mono⊩ {A} η a)

    ⟪S⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ C
    ⟪S⟫ {A} {B} {C} s₁ s₂ a = _⟪$⟫_ {B} {C} (_⟪$⟫_ {A} {B ▻ C} s₁ a) (_⟪$⟫_ {A} {B} s₂ a)

    ⟪S⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ (A ▻ B) ▻ A ▻ C
    ⟪S⟫′ {A} {B} {C} s₁ η s₂ η′ a = let s₁′ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                        s₂′ = mono⊩ {A ▻ B} η′ s₂
                                    in  ⟪S⟫ {A} {B} {C} s₁′ s₂′ a

    ⟪↓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
    ⟪↓⟫ s = sem (s refl⊆)

    _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A ∧ B
    _⟪,⟫′_ {A} {B} a η = _,_ (mono⊩ {A} η a)


  -- Forcing in a particular world of a particular model, for sequents.

  module _ {{_ : Model}} where
    infix 3 _⁏_⊩_⁏_⇒_
    _⁏_⊩_⁏_⇒_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Ty → Set
    Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A

    infix 3 _⁏_⊩_⁏_⇒⋆_
    _⁏_⊩_⁏_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
    Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Ξ = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ Ξ


  -- Entailment, or forcing in all worlds of all models, for sequents.

  infix 3 _⁏_⊨_
  _⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⁏ Δ ⇒ A

  infix 3 _⁏_⊨⋆_
  _⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
  Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⁏ Δ ⇒⋆ Ξ


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
    mlookup top     (γ , s) = sem (s refl⊆)
    mlookup (pop i) (γ , s) = mlookup i γ

    -- TODO: More equipment.
