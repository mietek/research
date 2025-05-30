{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module A201607.WIP2.BasicIS4.Semantics.Sketch7 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


record Model : Set₁ where
  field
    World : Set

    -- Zero : World

    _L_    : World → World → Set
    reflL  : ∀ {w} → w L w
    transL : ∀ {w w′ w″} → w L w′ → w′ L w″ → w L w″
    -- botL   : ∀ {w} → Zero L w

    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″
    -- botR   : ∀ {w} → Zero R w

    _[⊢]_   : World → Ty → Set
    mono[⊢] : ∀ {A w w′} → w L w′ × w R w′ → w [⊢] A → w′ [⊢] A

    _[⊢ⁿᶠ]_ : World → Ty → Set

    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w L w′ × w R w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

  _≤_ : World → World → Set
  w ≤ w′ = w L w′ × w R w′

  refl≤ : ∀ {w} → w ≤ w
  refl≤ = reflL , reflR

  trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
  trans≤ (η , θ) (η′ , θ′) = transL η η′ , transR θ θ′

  -- bot≤ : ∀ {w} → Zero ≤ w
  -- bot≤ = botL , botR

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  -- _R⨾≤_ : World → World → Set
  -- _R⨾≤_ = _R_ ⨾ _≤_

  -- refl≤⨾R : ∀ {w} → w ≤⨾R w
  -- refl≤⨾R {w} = w , (refl≤ , reflR)

  -- reflR⨾≤ : ∀ {w} → w R⨾≤ w
  -- reflR⨾≤ {w} = w , (reflR , refl≤)

  ≤⨾R→R : ∀ {v′ w} → w ≤⨾R v′ → w R v′
  ≤⨾R→R (w′ , ((η , θ) , θ′)) = transR θ θ′

  -- R⨾≤→R : ∀ {w v′} → w R⨾≤ v′ → w R v′
  -- R⨾≤→R (v , (θ , (η , θ′))) = transR θ θ′

  -- ≤⨾R→R⨾≤ : ∀ {w′ w} → w ≤⨾R w′ → w R⨾≤ w′
  -- ≤⨾R→R⨾≤ {w′} ξ,θ = w′ , (≤⨾R→R ξ,θ , refl≤)

  -- transR⨾≤ : ∀ {w′ w w″} → w R⨾≤ w′ → w′ R⨾≤ w″ → w R⨾≤ w″
  -- transR⨾≤ {w′} (v , (θ , ξ)) (v′ , (θ′ , ξ′)) = let v″ , (θ″ , ξ″) = ≤⨾R→R⨾≤ (w′ , (ξ , θ′))
  --                                                in  v″ , (transR θ θ″ , trans≤ ξ″ ξ′)

  ≤→R : ∀ {v′ w} → w ≤ v′ → w R v′
  ≤→R {v′} ξ = ≤⨾R→R (v′ , (ξ , reflR))

  -- R⨾≤→≤⨾R : ∀ {w v′} → w R⨾≤ v′ → w ≤⨾R v′
  -- R⨾≤→≤⨾R {w} θ,ξ = w , (refl≤ , R⨾≤→R θ,ξ)

  -- trans≤⨾R : ∀ {w′ w w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
  -- trans≤⨾R {w′} (v , (ξ , θ)) (v′ , (ξ′ , θ′)) = let v″ , (ξ″ , θ″) = R⨾≤→≤⨾R (w′ , (θ , ξ′))
  --                                                in  v″ , (trans≤ ξ ξ″ , transR θ″ θ′)

  -- ≤→R′ : ∀ {w v′} → w ≤ v′ → w R v′
  -- ≤→R′ {w} ξ = R⨾≤→R (w , (reflR , ξ))

  -- _≤⊓R_ : World → World → Set
  -- _≤⊓R_ = _≤_ ⊓ _R_

  -- _R⊓≤_ : World → World → Set
  -- _R⊓≤_ = _R_ ⊓ _≤_

  -- ≤⊓R→R⊓≤ : ∀ {w′ v} → w′ ≤⊓R v → v R⊓≤ w′
  -- ≤⊓R→R⊓≤ (w , (ξ , θ)) = w , (θ , ξ)

  -- R⊓≤→≤⊓R : ∀ {w′ v} → v R⊓≤ w′ → w′ ≤⊓R v
  -- R⊓≤→≤⊓R (w , (θ , ξ)) = w , (ξ , θ)

  -- infix 3 _≤⊔R_
  -- _≤⊔R_ : World → World → Set
  -- _≤⊔R_ = _≤_ ⊔ _R_

  -- infix 3 _R⊔≤_
  -- _R⊔≤_ : World → World → Set
  -- _R⊔≤_ = _R_ ⊔ _≤_

  -- ≤⊔R→R⊔≤ : ∀ {w′ v} → w′ ≤⊔R v → v R⊔≤ w′
  -- ≤⊔R→R⊔≤ (v′ , (ξ , θ)) = v′ , (θ , ξ)

  -- R⊔≤→≤⊔R : ∀ {w′ v} → v R⊔≤ w′ → w′ ≤⊔R v
  -- R⊔≤→≤⊔R (v′ , (θ , ξ)) = v′ , (ξ , θ)

  -- ≤⊓R→≤⊔R : ∀ {v w′} → w′ ≤⊓R v → v ≤⊔R w′
  -- ≤⊓R→≤⊔R {v} {w′} (w , ((η , θ) , θ′)) = {!!} , ({!!} , {!!})

  -- ≤⊔R→≤⊓R : ∀ {w′ v} → v ≤⊔R w′ → w′ ≤⊓R v
  -- ≤⊔R→≤⊓R (v′ , ((η , θ) , θ′)) = Zero , (bot≤ , botR)

open Model {{…}} public


module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′} → w′ L {!w!} → w R w′ → w′ [⊢] A × w′ ⊩ A
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {C} {w′ : World} → w ≤ w′ → (∀ {w″ : World} → w′ ≤ w″ → w″ ⊪ A → w″ [⊢ⁿᶠ] C) → w′ [⊢ⁿᶠ] C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A
