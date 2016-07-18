module BasicIPC.KripkeSemantics where

open import BasicIPC public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

open Model {{…}} public


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ∧ B = w ⊩ A ᴬᵍ∧ w ⊩ B
  w ⊩ ⊤    = ᴬᵍ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬᵍ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬᵍ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
  mono⊩ {A ∧ B} ξ s = ᴬᵍpair (mono⊩ {A} ξ (ᴬᵍfst s)) (mono⊩ {B} ξ (ᴬᵍsnd s))
  mono⊩ {⊤}    ξ s = ᴬᵍtt

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬᵍtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬᵍpair (mono⊩⋆ {Γ} ξ (ᴬᵍfst γ)) (mono⊩ {A} ξ (ᴬᵍsnd γ))


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A


-- Additional useful equipment.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     γ = ᴬᵍsnd γ
lookup (pop i) γ = lookup i (ᴬᵍfst γ)
