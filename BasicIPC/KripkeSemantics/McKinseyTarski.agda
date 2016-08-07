module BasicIPC.KripkeSemantics.McKinseyTarski where

open import BasicIPC public


-- Intuitionistic Kripke models, corresponding to the McKinsey-Tarski translation of IPC to S4.

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


-- Forcing in all models.

infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Ty → Set
w ⊩ α P   = w ⊩ᵅ P
w ⊩ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
w ⊩ A ∧ B = w ⊩ A × w ⊩ B
w ⊩ ⊤    = 𝟙

infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{_ : Model}} → World → Cx Ty → Set
w ⊩⋆ ⌀     = 𝟙
w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

mono⊩ : ∀ {{_ : Model}} {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
mono⊩ {α P}   ξ s       = mono⊩ᵅ ξ s
mono⊩ {A ▻ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
mono⊩ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
mono⊩ {⊤}    ξ ∙       = ∙

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