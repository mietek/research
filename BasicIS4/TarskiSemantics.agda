module BasicIS4.TarskiSemantics where

open import BasicIS4 public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Truth for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public


-- Closed syntax, inspired by Gabbay and Nanevski.

module TruthWithClosedBox (Box : Ty → Set) where

  -- Truth for propositions and contexts.

  module _ {{_ : Model}} where
    infix 3 ⊨_
    ⊨_ : Ty → Set
    ⊨ α P   = ⊨ᵅ P
    ⊨ A ▷ B = ⊨ A → ⊨ B
    ⊨ □ A   = Box A × ⊨ A
    ⊨ A ∧ B = ⊨ A × ⊨ B
    ⊨ ⊤    = 𝟙

    infix 3 ⊨⋆_
    ⊨⋆_ : Cx Ty → Set
    ⊨⋆ ⌀     = 𝟙
    ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


  -- Truth in all models.

  infix 3 _ᴹ⊨_
  _ᴹ⊨_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A

  infix 3 _ᴹ⊨⋆_
  _ᴹ⊨⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ᴹ⊨⋆ Π = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨⋆ Π

  infix 3 _⁏_ᴹ⊨_
  _⁏_ᴹ⊨_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨⋆ Δ → ⊨ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


-- Open syntax.

module TruthWithOpenBox (Box : Cx Ty → Ty → Set) where

  -- Truth for propositions and contexts.

  module _ {{_ : Model}} where
    infix 3 _⊨_
    _⊨_ : Cx Ty → Ty → Set
    Δ ⊨ α P   = ⊨ᵅ P
    Δ ⊨ A ▷ B = ∀ {Δ′} → Δ ⊆ Δ′ → Δ′ ⊨ A → Δ′ ⊨ B
    Δ ⊨ □ A   = ∀ {Δ′} → Δ ⊆ Δ′ → Box Δ′ A × Δ′ ⊨ A
    Δ ⊨ A ∧ B = Δ ⊨ A × Δ ⊨ B
    Δ ⊨ ⊤    = 𝟙

    infix 3 _⊨⋆_
    _⊨⋆_ : Cx Ty → Cx Ty → Set
    Δ ⊨⋆ ⌀     = 𝟙
    Δ ⊨⋆ Γ , A = Δ ⊨⋆ Γ × Δ ⊨ A


    -- Monotonicity with respect to context inclusion.

    mono⊨ : ∀ {A Δ Δ′} → Δ ⊆ Δ′ → Δ ⊨ A → Δ′ ⊨ A
    mono⊨ {α P}   θ s       = s
    mono⊨ {A ▷ B} θ f       = λ θ′ a → f (trans⊆ θ θ′) a
    mono⊨ {□ A}   θ □f      = λ θ′ → □f (trans⊆ θ θ′)
    mono⊨ {A ∧ B} θ (a , b) = mono⊨ {A} θ a , mono⊨ {B} θ b
    mono⊨ {⊤}    θ ∙       = ∙

    mono⊨⋆ : ∀ {Π Δ Δ′} → Δ ⊆ Δ′ → Δ ⊨⋆ Π → Δ′ ⊨⋆ Π
    mono⊨⋆ {⌀}     θ ∙        = ∙
    mono⊨⋆ {Π , A} θ (ts , t) = mono⊨⋆ {Π} θ ts , mono⊨ {A} θ t


  -- Truth in all models.

  infix 3 _ᴹ⊨_
  _ᴹ⊨_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⌀ ⊨⋆ Γ → ⌀ ⊨ A

  infix 3 _ᴹ⊨⋆_
  _ᴹ⊨⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ᴹ⊨⋆ Π = ∀ {{_ : Model}} → ⌀ ⊨⋆ Γ → ⌀ ⊨⋆ Π

  infix 3 _⁏_ᴹ⊨_
  _⁏_ᴹ⊨_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ᴹ⊨ A = ∀ {{_ : Model}} → ⌀ ⊨⋆ Γ → ⌀ ⊨⋆ Δ → Δ ⊨ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
