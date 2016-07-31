module BasicIS4.Regular.Gentzen.KripkeEquipment where

open import BasicIS4.Regular.Gentzen public


-- Worlds for the canonical model.

Worldᶜ : Set
Worldᶜ = Cx Ty


-- The canonical modal accessibility, based on the T axiom.

infix 3 _Rᶜ_
_Rᶜ_ : Worldᶜ → Worldᶜ → Set
w Rᶜ w′ = ∀ {A} → w ⊢ □ A → w′ ⊢ A

reflRᶜ : ∀ {w} → w Rᶜ w
reflRᶜ = down

transRᶜ : ∀ {w w′ w″} → w Rᶜ w′ → w′ Rᶜ w″ → w Rᶜ w″
transRᶜ ζ ζ′ = ζ′ ∘ ζ ∘ up

botRᶜ : ∀ {w} → ⌀ Rᶜ w
botRᶜ = mono⊢ bot⊆ ∘ down

liftRᶜ : ∀ {w} → w Rᶜ □⋆ w
liftRᶜ = down ∘ lift ∘ down


-- Frame conditions given by Božić and Došen, and by Ono.
--
--   zigzag:         zig:
--
--   w′  R   v′      w′  R   v′
--   ●───────●       ●───────●
--   │       ┊       │     ⋰
-- ≤ │       ┊ ≤   ≤ │   R
--   │       ┊       │ ⋰
--   ●╌╌╌╌╌╌╌◌       ●
--   w   R   v       w

zigRᶜ : ∀ {v′ w w′} → w′ Rᶜ v′ → w ⊆ w′ → w Rᶜ v′
zigRᶜ ζ ξ = ζ ∘ mono⊢ ξ

zigzagR⨾≤ᶜ : ∀ {v′ w w′} → w′ Rᶜ v′ → w ⊆ w′ → ∃ (λ v → w Rᶜ v × v ⊆ v′)
zigzagR⨾≤ᶜ {v′} ζ ξ = v′ , (zigRᶜ ζ ξ , refl⊆)

infix 3 _R⨾≤ᶜ_
_R⨾≤ᶜ_ : Worldᶜ → Worldᶜ → Set
_R⨾≤ᶜ_ = _Rᶜ_ ⨾ _⊆_

reflR⨾≤ᶜ : ∀ {w} → w R⨾≤ᶜ w
reflR⨾≤ᶜ {w} = w , (reflRᶜ , refl⊆)

transR⨾≤ᶜ : ∀ {w w′ w″} → w R⨾≤ᶜ w′ → w′ R⨾≤ᶜ w″ → w R⨾≤ᶜ w″
transR⨾≤ᶜ (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) = let v″ , (ζ″ , ξ″) = zigzagR⨾≤ᶜ ζ′ ξ
                                           in  v″ , (transRᶜ ζ ζ″ , trans⊆ ξ″ ξ′)


-- Frame condition given by Ewald et al. and Alechina et al., and a simplified condition.
--
--   zagzig:         zag:
--
--   w′  R   v′              v′
--   ◌╌╌╌╌╌╌╌●               ●
--   ┊       │             ⋰ ┊
-- ≤ ┊       │ ≤         R   ┊ ≤
--   ┊       │         ⋰     ┊
--   ●───────●       ●───────●
--   w   R   v       w   R   v

zagRᶜ : ∀ {w v v′} → v ⊆ v′ → w Rᶜ v → w Rᶜ v′
zagRᶜ {w} ξ ζ = mono⊢ ξ ∘ ζ

zagzig≤⨾Rᶜ : ∀ {w v v′} → v ⊆ v′ → w Rᶜ v → ∃ (λ w′ → w ⊆ w′ × w′ Rᶜ v′)
zagzig≤⨾Rᶜ {w} ξ ζ = w , (refl⊆ , zagRᶜ ξ ζ)

infix 3 _≤⨾Rᶜ_
_≤⨾Rᶜ_ : Worldᶜ → Worldᶜ → Set
_≤⨾Rᶜ_ = _⊆_ ⨾ _Rᶜ_

refl≤⨾Rᶜ : ∀ {w} → w ≤⨾Rᶜ w
refl≤⨾Rᶜ {w} = w , (refl⊆ , reflRᶜ)

trans≤⨾Rᶜ : ∀ {w w′ w″} → w ≤⨾Rᶜ w′ → w′ ≤⨾Rᶜ w″ → w ≤⨾Rᶜ w″
trans≤⨾Rᶜ (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) = let v″ , (ξ″ , ζ″) = zagzig≤⨾Rᶜ ξ′ ζ
                                           in  v″ , (trans⊆ ξ ξ″ , transRᶜ ζ″ ζ′)


-- Frame condition given by Ewald et al., and a dual condition.
--
--   zap:            zup:
--
--   w′  R   v′      w′  R   v′
--   ●╌╌╌╌╌╌╌◌       ●───────●
--   │       ┊       ┊       │
-- ≤ │       ┊ ≤   ≤ ┊       │ ≤
--   │       ┊       ┊       │
--   ●───────●       ◌╌╌╌╌╌╌╌●
--   w   R   v       w   R   v

-- NOTE: This could be a more precise supremum.
zapRᶜ : ∀ {v w′ w} → w Rᶜ v → w ⊆ w′ → ∃ (λ v′ → w′ Rᶜ v′ × v ⊆ v′)
zapRᶜ {v} {w′} ζ ξ = (w′ ⧺ v) , (mono⊢ (weak⊆⧺ₗ v) ∘ down , weak⊆⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupRᶜ : ∀ {w′ v v′} → v ⊆ v′ → w′ Rᶜ v′ → ∃ (λ w → w ⊆ w′ × w Rᶜ v)
zupRᶜ ξ ζ = ⌀ , (bot⊆ , botRᶜ)
