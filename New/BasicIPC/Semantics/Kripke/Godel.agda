-- Kripke-style possible worlds semantics, based on the Gödel translation.

module New.BasicIPC.Semantics.Kripke.Godel where

open import New.BasicIPC.Syntax.Common public


-- Kripke-Gödel models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions.
    _⊩ᵅ_ : World → Atom → Set

open Model {{…}} public


-- Forcing in a particular model.

infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Ty → Set
w ⊩ α P   = ∀ {w′} → w ≤ w′ → w′ ⊩ᵅ P
w ⊩ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
w ⊩ A ∧ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A × w′ ⊩ B
w ⊩ ⊤    = ∀ {w′} → w ≤ w′ → 𝟙

infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{_ : Model}} → World → Cx Ty → Set
w ⊩⋆ ⌀     = 𝟙
w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

mono⊩ : ∀ {{_ : Model}} {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
mono⊩ {α P}   ξ s = λ ξ′ → s (trans≤ ξ ξ′)
mono⊩ {A ▻ B} ξ s = λ ξ′ → s (trans≤ ξ ξ′)
mono⊩ {A ∧ B} ξ s = λ ξ′ → s (trans≤ ξ ξ′)
mono⊩ {⊤}    ξ s = λ ξ′ → ∙

mono⊩⋆ : ∀ {{_ : Model}} {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
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
lookup (pop i) (γ , b) = lookup i γ
