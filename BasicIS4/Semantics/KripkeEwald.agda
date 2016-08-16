-- Kripke-style possible worlds semantics, after Ewald, Servi, and Plotkin-Stirling.

module BasicIS4.Semantics.KripkeEwald where

open import BasicIS4.Syntax.Common public


-- Intuitionistic modal Kripke models, with Ewald frame conditions.

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


  -- Composition of accessibility.

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  _≤⊓R_ : World → World → Set
  _≤⊓R_ = _≤_ ⊓ _R_

  _≤⊔R_ : World → World → Set
  _≤⊔R_ = _≤_ ⊔ _R_


  -- Infimum-to-supremum condition.
  --
  --   w′          →   w′      v′
  --   ●           →   ●───R───◌
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ◌───R───●   →           ●
  --   w       v   →           v

  field
    ≤⊓R→≤⊔R : ∀ {v w′} → w′ ≤⊓R v → v ≤⊔R w′


  -- Minor brilliance condition.
  --
  --           v′  →   w′      v′
  --           ●   →   ◌───R───●
  --           │   →   │
  --      ζ,ξ  ≤   →   ≤
  --           │   →   │
  --   ●───R───◌   →   ●
  --   w       v   →   w
  --
  --           v′      w″  →   v″              w″
  --           ◌───R───●   →   ◌───────R───────●
  --           │           →   │
  --           ≤  ξ′,ζ′    →   │
  --   v       │           →   │
  --   ◌───R───●           →   ≤
  --   │       w′          →   │
  --   ≤  ξ,ζ              →   │
  --   │                   →   │
  --   ●                   →   ●
  --   w                   →   w

  field
    R⨾≤→≤⨾R : ∀ {w v′} → w R⨾≤ v′ → w ≤⨾R v′

  refl≤⨾R : ∀ {w} → w ≤⨾R w
  refl≤⨾R {w} = w , (refl≤ , reflR)

  trans≤⨾R : ∀ {w′ w w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
  trans≤⨾R {w′} (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
    let v″ , (ξ″ , ζ″) = R⨾≤→≤⨾R (w′ , (ζ , ξ′))
    in  v″ , (trans≤ ξ ξ″ , transR ζ″ ζ′)

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A   = ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩ A
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = 𝟙
  w ⊩⋆ Π , A = w ⊩⋆ Π × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s       = mono⊩ᵅ ξ s
  mono⊩ {A ▻ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ □f      = λ ξ′ ζ → □f (trans≤ ξ ξ′) ζ
  mono⊩ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
  mono⊩ {⊤}    ξ ∙       = ∙

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ ∙       = ∙
  mono⊩⋆ {Γ , A} ξ (γ , a) = mono⊩⋆ {Γ} ξ γ , mono⊩ {A} ξ a


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B w} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
  f ⟪$⟫ a = f refl≤ a

  ⟪const⟫ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A
  ⟪const⟫ {A} a ξ = const (mono⊩ {A} ξ a)

  ⟪ap⟫′ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ {A} {B} {C} f ξ g ξ′ a = let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                                     g′ = mono⊩ {A ▻ B} ξ′ g
                                 in  (f′ refl≤ a) refl≤ (g′ refl≤ a)

  ⟪ap⟫ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ A ▻ B → w ⊩ A → w ⊩ C
  ⟪ap⟫ {A} {B} {C} f g a = ⟪ap⟫′ {A} {B} {C} f refl≤ g refl≤ a

  _⟪,⟫′_ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a ξ b = let a′ = mono⊩ {A} ξ a
                         in  a′ , b

  _⟪,⟫_ : ∀ {A B w} → w ⊩ A → w ⊩ B → w ⊩ A ∧ B
  _⟪,⟫_ {A} {B} a b = _⟪,⟫′_ {A} {B} a refl≤ b


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : World → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : World → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Π = w ⊩⋆ Γ → w ⊩⋆ Π


-- Forcing in all world of all models, for sequents.

infix 3 ∀ᴹʷ⊩_⇒_
∀ᴹʷ⊩_⇒_ : Cx Ty → Ty → Set₁
∀ᴹʷ⊩ Γ ⇒ A = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒ A

infix 3 ∀ᴹʷ⊩_⇒⋆_
∀ᴹʷ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set₁
∀ᴹʷ⊩ Γ ⇒⋆ Π = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒⋆ Π

infix 3 ∀ᴹʷ⊩_⁏_⇒_
∀ᴹʷ⊩_⁏_⇒_ : Cx Ty → Cx Ty → Ty → Set₁
∀ᴹʷ⊩ Γ ⁏ Δ ⇒ A = ∀ {{_ : Model}} {w : World}
                   → w ⊩⋆ Γ → (∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ Δ) → w ⊩ A


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
