module BasicIS4.KripkeSemantics.EwaldEtAl where

open import BasicIS4 public


-- Intuitionistic modal Kripke models, following Ewald, Servi, Plotkin, and Stirling, after Simpson.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Modal accessibility; preorder.
    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

    -- NOTE: Additional frame conditions.
    --
    --   w′  R  v′      w′  R  v′
    --   ●╌╌╌╌╌╌◌       ◌╌╌╌╌╌╌●
    --   │      ┊       ┊      │
    -- ≤ │   ₁  ┊ ≤   ≤ ┊   ₂  │ ≤
    --   │      ┊       ┊      │
    --   ●──────●       ●──────●
    --   w   R  v       w   R  v
    --
    slice  : ∀ {v w w′} → w R v → w ≤ w′ → ∃ (λ v′ → w′ R v′ × v ≤ v′)
    cut≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  refl≤⨾R : ∀ {w} → w ≤⨾R w
  refl≤⨾R {w} = w , (refl≤ , reflR)

  trans≤⨾R : ∀ {w w′ w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
  trans≤⨾R (a , (ξ , ζ)) (b , (ξ′ , ζ′)) =
    let c , (ξ″ , ζ″) = cut≤⨾R ξ′ ζ
    in  c , (trans≤ ξ ξ″ , transR ζ″ ζ′)

open Model {{…}} public


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A   = ∀ {w′ v′} → w ≤ w′ → w′ R v′ → v′ ⊩ A
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = Top

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = Top
  w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s       = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ □f      = λ ξ′ ζ → □f (trans≤ ξ ξ′) ζ
  mono⊩ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
  mono⊩ {⊤}    ξ ∙       = ∙

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ ∙       = ∙
  mono⊩⋆ {Γ , A} ξ (γ , a) = mono⊩⋆ {Γ} ξ γ , mono⊩ {A} ξ a


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A

infix 3 _ᴹ⊩⋆_
_ᴹ⊩⋆_ : Cx Ty → Cx Ty → Set₁
Γ ᴹ⊩⋆ Π = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Π


-- Additional useful equipment.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     (γ , a) = a
lookup (pop i) (γ , a) = lookup i γ
