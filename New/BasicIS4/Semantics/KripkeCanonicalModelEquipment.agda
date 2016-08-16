module New.BasicIS4.Semantics.KripkeCanonicalModelEquipment where

open import New.BasicIS4.Syntax.Common public




module SyntacticComponent (_⊢_   : Cx Ty → Ty → Set)
                          (mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A)
                          (up     : ∀ {A Γ} → Γ ⊢ (□ A) → Γ ⊢ (□ □ A))
                          (down   : ∀ {A Γ} → Γ ⊢ (□ A) → Γ ⊢ A)
                          (lift   : ∀ {A Γ} → Γ ⊢ A → (□⋆ Γ) ⊢ (□ A)) where


  -- Worlds for the canonical model.

  Worldᶜ : Set
  Worldᶜ = Cx Ty


  -- The canonical intuitionistic accessibility.

  infix 3 _≤ᶜ_
  _≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤ᶜ_ = _⊆_

  refl≤ᶜ : ∀ {w} → w ≤ᶜ w
  refl≤ᶜ = refl⊆

  trans≤ᶜ : ∀ {w w′ w″} → w ≤ᶜ w′ → w′ ≤ᶜ w″ → w ≤ᶜ w″
  trans≤ᶜ = trans⊆

  bot≤ᶜ : ∀ {w} → ⌀ ≤ᶜ w
  bot≤ᶜ = bot⊆


  -- The canonical modal accessibility, based on the T axiom.

  infix 3 _Rᶜ_
  _Rᶜ_ : Worldᶜ → Worldᶜ → Set
  w Rᶜ w′ = ∀ {A} → w ⊢ (□ A) → w′ ⊢ A

  reflRᶜ : ∀ {w} → w Rᶜ w
  reflRᶜ = down

  transRᶜ : ∀ {w w′ w″} → w Rᶜ w′ → w′ Rᶜ w″ → w Rᶜ w″
  transRᶜ ζ ζ′ = ζ′ ∘ ζ ∘ up

  botRᶜ : ∀ {w} → ⌀ Rᶜ w
  botRᶜ = mono⊢ bot≤ᶜ ∘ down

  liftRᶜ : ∀ {w} → w Rᶜ □⋆ w
  liftRᶜ = down ∘ lift ∘ down


  -- Composition of accessibility.

  infix 3 _≤⨾Rᶜ_
  _≤⨾Rᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⨾Rᶜ_ = _≤ᶜ_ ⨾ _Rᶜ_

  infix 3 _R⨾≤ᶜ_
  _R⨾≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _R⨾≤ᶜ_ = _Rᶜ_ ⨾ _≤ᶜ_

  refl≤⨾Rᶜ : ∀ {w} → w ≤⨾Rᶜ w
  refl≤⨾Rᶜ {w} = w , (refl≤ᶜ , reflRᶜ)

  reflR⨾≤ᶜ : ∀ {w} → w R⨾≤ᶜ w
  reflR⨾≤ᶜ {w} = w , (reflRᶜ , refl≤ᶜ)


  -- Persistence condition, after Iemhoff; included by Ono.
  --
  --   w′      v′  →           v′
  --   ◌───R───●   →           ●
  --   │           →         ╱
  --   ≤  ξ,ζ      →       R
  --   │           →     ╱
  --   ●           →   ●
  --   w           →   w

  ≤⨾R→Rᶜ : ∀ {v′ w} → w ≤⨾Rᶜ v′ → w Rᶜ v′
  ≤⨾R→Rᶜ (w′ , (ξ , ζ)) = ζ ∘ mono⊢ ξ


  -- Brilliance condition, after Iemhoff.
  --
  --           v′  →           v′
  --           ●   →           ●
  --           │   →         ╱
  --      ζ,ξ  ≤   →       R
  --           │   →     ╱
  --   ●───R───◌   →   ●
  --   w       v   →   w

  R⨾≤→Rᶜ : ∀ {w v′} → w R⨾≤ᶜ v′ → w Rᶜ v′
  R⨾≤→Rᶜ (v , (ζ , ξ)) = mono⊢ ξ ∘ ζ


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

  ≤⨾R→R⨾≤ᶜ : ∀ {v′ w} → w ≤⨾Rᶜ v′ → w R⨾≤ᶜ v′
  ≤⨾R→R⨾≤ᶜ {v′} ξ,ζ = v′ , (≤⨾R→Rᶜ ξ,ζ , refl≤ᶜ)

  transR⨾≤ᶜ : ∀ {w′ w w″} → w R⨾≤ᶜ w′ → w′ R⨾≤ᶜ w″ → w R⨾≤ᶜ w″
  transR⨾≤ᶜ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) =
    let v″ , (ζ″ , ξ″) = ≤⨾R→R⨾≤ᶜ (w′ , (ξ , ζ′))
    in  v″ , (transRᶜ ζ ζ″ , trans≤ᶜ ξ″ ξ′)

  ≤→Rᶜ : ∀ {v′ w} → w ≤ᶜ v′ → w Rᶜ v′
  ≤→Rᶜ {v′} ξ = ≤⨾R→Rᶜ (v′ , (ξ , reflRᶜ))


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

  R⨾≤→≤⨾Rᶜ : ∀ {w v′} → w R⨾≤ᶜ v′ → w ≤⨾Rᶜ v′
  R⨾≤→≤⨾Rᶜ {w} ζ,ξ = w , (refl≤ᶜ , R⨾≤→Rᶜ ζ,ξ)

  trans≤⨾Rᶜ : ∀ {w′ w w″} → w ≤⨾Rᶜ w′ → w′ ≤⨾Rᶜ w″ → w ≤⨾Rᶜ w″
  trans≤⨾Rᶜ {w′} (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
    let v″ , (ξ″ , ζ″) = R⨾≤→≤⨾Rᶜ (w′ , (ζ , ξ′))
    in  v″ , (trans≤ᶜ ξ ξ″ , transRᶜ ζ″ ζ′)

  ≤→Rᶜ′ : ∀ {w v′} → w ≤ᶜ v′ → w Rᶜ v′
  ≤→Rᶜ′ {w} ξ = R⨾≤→Rᶜ (w , (reflRᶜ , ξ))


  -- Infimum (greatest lower bound) of accessibility.
  --
  --   w′
  --   ●
  --   │
  --   ≤  ξ,ζ
  --   │
  --   ◌───R───●
  --   w       v

  infix 3 _≤⊓Rᶜ_
  _≤⊓Rᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⊓Rᶜ_ = _≤ᶜ_ ⊓ _Rᶜ_

  infix 3 _R⊓≤ᶜ_
  _R⊓≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _R⊓≤ᶜ_ = _Rᶜ_ ⊓ _≤ᶜ_

  ≤⊓R→R⊓≤ᶜ : ∀ {w′ v} → w′ ≤⊓Rᶜ v → v R⊓≤ᶜ w′
  ≤⊓R→R⊓≤ᶜ (w , (ξ , ζ)) = w , (ζ , ξ)

  R⊓≤→≤⊓Rᶜ : ∀ {w′ v} → v R⊓≤ᶜ w′ → w′ ≤⊓Rᶜ v
  R⊓≤→≤⊓Rᶜ (w , (ζ , ξ)) = w , (ξ , ζ)


  -- Supremum (least upper bound) of accessibility.
  --
  --   w′      v′
  --   ●───R───◌
  --           │
  --      ξ,ζ  ≤
  --           │
  --           ●
  --           v

  infix 3 _≤⊔Rᶜ_
  _≤⊔Rᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⊔Rᶜ_ = _≤ᶜ_ ⊔ _Rᶜ_

  infix 3 _R⊔≤ᶜ_
  _R⊔≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _R⊔≤ᶜ_ = _Rᶜ_ ⊔ _≤ᶜ_

  ≤⊔R→R⊔≤ᶜ : ∀ {w′ v} → w′ ≤⊔Rᶜ v → v R⊔≤ᶜ w′
  ≤⊔R→R⊔≤ᶜ (v′ , (ξ , ζ)) = v′ , (ζ , ξ)

  R⊔≤→≤⊔Rᶜ : ∀ {w′ v} → v R⊔≤ᶜ w′ → w′ ≤⊔Rᶜ v
  R⊔≤→≤⊔Rᶜ (v′ , (ζ , ξ)) = v′ , (ξ , ζ)


  -- Infimum-to-supremum condition, included by Ewald et al.
  --
  --   w′          →   w′      v′
  --   ●           →   ●───R───◌
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ◌───R───●   →           ●
  --   w       v   →           v

  -- NOTE: This could be more precise.
  ≤⊓R→≤⊔Rᶜ : ∀ {v w′} → w′ ≤⊓Rᶜ v → v ≤⊔Rᶜ w′
  ≤⊓R→≤⊔Rᶜ {v} {w′} (w , (ξ , ζ)) =
    (w′ ⧺ v) , (weak⊆⧺ᵣ , mono⊢ (weak⊆⧺ₗ v) ∘ down)


  -- Supremum-to-infimum condition.
  --
  --   w′      v′  →   w′
  --   ●───R───◌   →   ●
  --           │   →   │
  --      ξ,ζ  ≤   →   ≤
  --           │   →   │
  --           ●   →   ◌───R───●
  --           v   →   w       v

  -- NOTE: This could be more precise.
  ≤⊔R→≤⊓Rᶜ : ∀ {w′ v} → v ≤⊔Rᶜ w′ → w′ ≤⊓Rᶜ v
  ≤⊔R→≤⊓Rᶜ (v′ , (ξ , ζ)) = ⌀ , (bot≤ᶜ , botRᶜ)
