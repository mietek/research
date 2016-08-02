module BasicIS4.KripkeSemantics where

open import BasicIS4 public


-- Intuitionistic modal Kripke models, including all known frame conditions.

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


    -- Persistence condition, after Iemhoff; included by Ono.
    --
    --   w′      v′  →           v′
    --   ◌───R───●   →           ●
    --   │           →         ╱
    --   ≤  ξ,ζ      →       R
    --   │           →     ╱
    --   ●           →   ●
    --   w           →   w

    ≤⨾R→R : ∀ {v′ w} → (_≤_ ⨾ _R_) w v′ → w R v′


    -- Brilliance condition, after Iemhoff.
    --
    --           v′  →           v′
    --           ●   →           ●
    --           │   →         ╱
    --      ζ,ξ  ≤   →       R
    --           │   →     ╱
    --   ●───R───◌   →   ●
    --   w       v   →   w

    R⨾≤→R : ∀ {w v′} → (_R_ ⨾ _≤_) w v′ → w R v′


    -- Infimum-to-supremum condition, included by Ewald et al.
    --
    --   w′          →   w′      v′
    --   ●           →   ●───R───◌
    --   │           →           │
    --   ≤  ξ,ζ      →           ≤
    --   │           →           │
    --   ◌───R───●   →           ●
    --   w       v   →           v

    ≤⊓R→≤⊔R : ∀ {v w′} → (_≤_ ⊓ _R_) w′ v → (_≤_ ⊔ _R_) v w′


    -- Supremum-to-infimum condition.
    --
    --   w′      v′  →   w′
    --   ●───R───◌   →   ●
    --           │   →   │
    --      ξ,ζ  ≤   →   ≤
    --           │   →   │
    --           ●   →   ◌───R───●
    --           v   →   w       v

    ≤⊔R→≤⊓R : ∀ {w′ v} → (_≤_ ⊔ _R_) v w′ → (_≤_ ⊓ _R_) w′ v


  -- Composition of accessibility.

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  refl≤⨾R : ∀ {w} → w ≤⨾R w
  refl≤⨾R {w} = w , (refl≤ , reflR)

  reflR⨾≤ : ∀ {w} → w R⨾≤ w
  reflR⨾≤ {w} = w , (reflR , refl≤)


  -- Minor persistence condition, included by Božić and Došen.
  --
  --   w′      v′  →           v′
  --   ◌───R───●   →           ●
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ●           →   ●───R───◌
  --   w           →   w       v
  --
  --                   w″  →                   w″
  --                   ●   →                   ●
  --                   │   →                   │
  --             ξ′,ζ′ ≤   →                   │
  --                   │   →                   │
  --           ●───R───◌   →                   ≤
  --           │       v′  →                   │
  --      ξ,ζ  ≤           →                   │
  --           │           →                   │
  --   ●───R───◌           →   ●───────R───────◌
  --   w       v           →   w               v″

  ≤⨾R→R⨾≤ : ∀ {v′ w} → w ≤⨾R v′ → w R⨾≤ v′
  ≤⨾R→R⨾≤ {v′} ξ,ζ = v′ , (≤⨾R→R ξ,ζ , refl≤)

  transR⨾≤ : ∀ {w′ w w″} → w R⨾≤ w′ → w′ R⨾≤ w″ → w R⨾≤ w″
  transR⨾≤ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) =
    let v″ , (ζ″ , ξ″) = ≤⨾R→R⨾≤ (w′ , (ξ , ζ′))
    in  v″ , (transR ζ ζ″ , trans≤ ξ″ ξ′)

  ≤→R : ∀ {v′ w} → w ≤ v′ → w R v′
  ≤→R {v′} ξ = ≤⨾R→R (v′ , (ξ , reflR))


  -- Minor brilliance condition, included by Ewald et al. and Alechina et al.
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

  R⨾≤→≤⨾R : ∀ {w v′} → w R⨾≤ v′ → w ≤⨾R v′
  R⨾≤→≤⨾R {w} ζ,ξ = w , (refl≤ , R⨾≤→R ζ,ξ)

  trans≤⨾R : ∀ {w′ w w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
  trans≤⨾R {w′} (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
    let v″ , (ξ″ , ζ″) = R⨾≤→≤⨾R (w′ , (ζ , ξ′))
    in  v″ , (trans≤ ξ ξ″ , transR ζ″ ζ′)

  ≤→R′ : ∀ {w v′} → w ≤ v′ → w R v′
  ≤→R′ {w} ξ = R⨾≤→R (w , (reflR , ξ))


  -- Infimum (greatest lower bound) of accessibility.
  --
  --   w′
  --   ●
  --   │
  --   ≤  ξ,ζ
  --   │
  --   ◌───R───●
  --   w       v

  _≤⊓R_ : World → World → Set
  _≤⊓R_ = _≤_ ⊓ _R_

  _R⊓≤_ : World → World → Set
  _R⊓≤_ = _R_ ⊓ _≤_

  ≤⊓R→R⊓≤ : ∀ {w′ v} → w′ ≤⊓R v → v R⊓≤ w′
  ≤⊓R→R⊓≤ (w , (ξ , ζ)) = w , (ζ , ξ)

  R⊓≤→≤⊓R : ∀ {w′ v} → v R⊓≤ w′ → w′ ≤⊓R v
  R⊓≤→≤⊓R (w , (ζ , ξ)) = w , (ξ , ζ)


  -- Supremum (least upper bound) of accessibility.
  --
  --   w′      v′
  --   ●───R───◌
  --           │
  --      ξ,ζ  ≤
  --           │
  --           ●
  --           v

  _≤⊔R_ : World → World → Set
  _≤⊔R_ = _≤_ ⊔ _R_

  _R⊔≤_ : World → World → Set
  _R⊔≤_ = _R_ ⊔ _≤_

  ≤⊔R→R⊔≤ : ∀ {w′ v} → w′ ≤⊔R v → v R⊔≤ w′
  ≤⊔R→R⊔≤ (v′ , (ξ , ζ)) = v′ , (ζ , ξ)

  R⊔≤→≤⊔R : ∀ {w′ v} → v R⊔≤ w′ → w′ ≤⊔R v
  R⊔≤→≤⊔R (v′ , (ζ , ξ)) = v′ , (ξ , ζ)

open Model {{…}} public


-- Forcing with only modal accessibility in the necessity case.

module RegularForcing where
  module _ {{_ : Model}} where
    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ α P   = w ⊩ᵅ P
    w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    -- NOTE: Only modal accessibility here.
    w ⊩ □ A   = ∀ {v′} → w R v′ → v′ ⊩ A
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
    mono⊩ {□ A}   ξ □f      = λ ζ → □f (transR (≤→R ξ) ζ)
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

  infix 3 _⁏_ᴹ⊩_
  _⁏_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World}
                → w ⊩⋆ Γ → (∀ {v′} → w R v′ → v′ ⊩⋆ Δ) → w ⊩ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


-- Forcing with both intuitionistic and modal accessibility in the necessity case.

module DualRelationForcing where
  module _ {{_ : Model}} where
    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ α P   = w ⊩ᵅ P
    w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    -- NOTE: Both intuitionistic and modal accessibility here.
    w ⊩ □ A   = ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩ A
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

  infix 3 _⁏_ᴹ⊩_
  _⁏_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
  Γ ⁏ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World}
                → w ⊩⋆ Γ → (∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ Δ) → w ⊩ A


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
