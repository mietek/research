-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
-- Implicit syntax.

module BasicIS4.Semantics.TarskiOvergluedDyadicImplicit where

open import BasicIS4.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_    : Cx² Ty Ty → Atom → Set
    mono²⊩ᵅ : ∀ {P Π Π′} → Π ⊆² Π′ → Π ⊩ᵅ P → Π′ ⊩ᵅ P

open Model {{…}} public




module ImplicitSyntax
    (_[⊢]_    : Cx² Ty Ty → Ty → Set)
    (mono²[⊢] : ∀ {A Π Π′}  → Π ⊆² Π′ → Π [⊢] A → Π′ [⊢] A)
  where


  -- Forcing in a particular model.

  module _ {{_ : Model}} where
    infix 3 _⊩_
    _⊩_ : Cx² Ty Ty → Ty → Set
    Π ⊩ α P   = Glue (Π [⊢] (α P)) (Π ⊩ᵅ P)
    Π ⊩ A ▻ B = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] (A ▻ B)) (Π′ ⊩ A → Π′ ⊩ B)
    Π ⊩ □ A   = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] (□ A)) (Π′ ⊩ A)
    Π ⊩ A ∧ B = Π ⊩ A × Π ⊩ B
    Π ⊩ ⊤    = 𝟙

    infix 3 _⊩⋆_
    _⊩⋆_ : Cx² Ty Ty → Cx Ty → Set
    Π ⊩⋆ ∅     = 𝟙
    Π ⊩⋆ Ξ , A = Π ⊩⋆ Ξ × Π ⊩ A


  -- Monotonicity with respect to context inclusion.

  module _ {{_ : Model}} where
    mono²⊩ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊩ A → Π′ ⊩ A
    mono²⊩ {α P}   ψ s = mono²[⊢] ψ (syn s) ⅋ mono²⊩ᵅ ψ (sem s)
    mono²⊩ {A ▻ B} ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
    mono²⊩ {□ A}   ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
    mono²⊩ {A ∧ B} ψ s = mono²⊩ {A} ψ (π₁ s) , mono²⊩ {B} ψ (π₂ s)
    mono²⊩ {⊤}    ψ s = ∙

    mono²⊩⋆ : ∀ {Ξ Π Π′} → Π ⊆² Π′ → Π ⊩⋆ Ξ → Π′ ⊩⋆ Ξ
    mono²⊩⋆ {∅}     ψ ∙        = ∙
    mono²⊩⋆ {Ξ , A} ψ (ts , t) = mono²⊩⋆ ψ ts , mono²⊩ {A} ψ t


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B Π} → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ B
    s ⟪$⟫ a = sem (s refl⊆²) a

    ⟪S⟫ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ C
    ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

    ⟪↓⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ A
    ⟪↓⟫ s = sem (s refl⊆²)


  -- Forcing in a particular world of a particular model, for sequents.

  module _ {{_ : Model}} where
    infix 3 _⊩_⇒_
    _⊩_⇒_ : Cx² Ty Ty → Cx² Ty Ty → Ty → Set
    Π ⊩ Γ ⁏ Δ ⇒ A = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩ A

    infix 3 _⊩_⇒⋆_
    _⊩_⇒⋆_ : Cx² Ty Ty → Cx² Ty Ty → Cx Ty → Set
    Π ⊩ Γ ⁏ Δ ⇒⋆ Ξ = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩⋆ Ξ


  -- Entailment, or forcing in all worlds of all models, for sequents.

  infix 3 _⊨_
  _⊨_ : Cx² Ty Ty → Ty → Set₁
  Π ⊨ A = ∀ {{_ : Model}} {w : Cx² Ty Ty} → w ⊩ Π ⇒ A

  infix 3 _⊨⋆_
  _⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
  Π ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx² Ty Ty} → w ⊩ Π ⇒⋆ Ξ


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    mlookup : ∀ {A Δ w} → A ∈ Δ → w ⊩⋆ □⋆ Δ → w ⊩ A
    mlookup top     (γ , s) = sem (s refl⊆²)
    mlookup (pop i) (γ , s) = mlookup i γ

    -- TODO: More equipment.
