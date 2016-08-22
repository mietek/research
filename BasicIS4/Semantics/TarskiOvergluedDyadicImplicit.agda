-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
-- Implicit syntax.

module BasicIS4.Semantics.TarskiOvergluedDyadicImplicit where

open import BasicIS4.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P
    mmono⊩ᵅ : ∀ {P Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ᵅ P → Γ ⁏ Δ′ ⊩ᵅ P

open Model {{…}} public




module ImplicitSyntax
    (_⁏_[⊢]_  : Cx Ty → Cx Ty → Ty → Set)
    (mono[⊢]  : ∀ {A Γ Γ′ Δ}  → Γ ⊆ Γ′ → Γ ⁏ Δ [⊢] A → Γ′ ⁏ Δ [⊢] A)
    (mmono[⊢] : ∀ {A Γ Δ Δ′}  → Δ ⊆ Δ′ → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ′ [⊢] A)
  where


  -- Forcing in a particular model.

  module _ {{_ : Model}} where
    infix 3 _⁏_⊩_
    _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
    Γ ⁏ Δ ⊩ α P   = Glue (Γ ⁏ Δ [⊢] (α P)) (Γ ⁏ Δ ⊩ᵅ P)
    Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → Glue (Γ′ ⁏ Δ′ [⊢] (A ▻ B)) (Γ′ ⁏ Δ′ ⊩ A → Γ′ ⁏ Δ′ ⊩ B)
    Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → Glue (Γ′ ⁏ Δ′ [⊢] (□ A)) (Γ′ ⁏ Δ′ ⊩ A)
    Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
    Γ ⁏ Δ ⊩ ⊤    = 𝟙

    infix 3 _⁏_⊩⋆_
    _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
    Γ ⁏ Δ ⊩⋆ ⌀     = 𝟙
    Γ ⁏ Δ ⊩⋆ Ξ , A = Γ ⁏ Δ ⊩⋆ Ξ × Γ ⁏ Δ ⊩ A


  -- Monotonicity with respect to context inclusion.

  module _ {{_ : Model}} where
    mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
    mono⊩ {α P}   η s = mono[⊢] η (syn s) ⅋ mono⊩ᵅ η (sem s)
    mono⊩ {A ▻ B} η s = λ η′ θ → s (trans⊆ η η′) θ
    mono⊩ {□ A}   η s = λ η′ θ → s (trans⊆ η η′) θ
    mono⊩ {A ∧ B} η s = mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s)
    mono⊩ {⊤}    η s = ∙

    mono⊩⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Ξ → Γ′ ⁏ Δ ⊩⋆ Ξ
    mono⊩⋆ {⌀}     η ∙        = ∙
    mono⊩⋆ {Ξ , A} η (ts , t) = mono⊩⋆ {Ξ} η ts , mono⊩ {A} η t


  -- Monotonicity with respect to modal context inclusion.

  module _ {{_ : Model}} where
    mmono⊩ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ′ ⊩ A
    mmono⊩ {α P}   θ s = mmono[⊢] θ (syn s) ⅋ mmono⊩ᵅ θ (sem s)
    mmono⊩ {A ▻ B} θ s = λ η θ′ → s η (trans⊆ θ θ′)
    mmono⊩ {□ A}   θ s = λ η θ′ → s η (trans⊆ θ θ′)
    mmono⊩ {A ∧ B} θ s = mmono⊩ {A} θ (π₁ s) , mmono⊩ {B} θ (π₂ s)
    mmono⊩ {⊤}    θ s = ∙

    mmono⊩⋆ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ′ ⊩⋆ Ξ
    mmono⊩⋆ {⌀}     η ∙        = ∙
    mmono⊩⋆ {Ξ , A} η (ts , t) = mmono⊩⋆ {Ξ} η ts , mmono⊩ {A} η t


  -- Combined monotonicity.

  module _ {{_ : Model}} where
    mono²⊩ : ∀ {A Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ′ ⊩ A
    mono²⊩ {A} (η , θ) = mono⊩ {A} η ∘ mmono⊩ {A} θ

    mono²⊩⋆ : ∀ {Ξ Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Ξ → Γ′ ⁏ Δ′ ⊩⋆ Ξ
    mono²⊩⋆ {Ξ} (η , θ) = mono⊩⋆ {Ξ} η ∘ mmono⊩⋆ {Ξ} θ


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
    s ⟪$⟫ a = sem (s refl⊆ refl⊆) a

    ⟪S⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ C
    ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

    ⟪↓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
    ⟪↓⟫ s = sem (s refl⊆ refl⊆)


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
  Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A

  infix 3 _⁏_⊨⋆_
  _⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
  Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Ξ


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
    mlookup top     (γ , s) = sem (s refl⊆ refl⊆)
    mlookup (pop i) (γ , s) = mlookup i γ

    -- TODO: More equipment.
