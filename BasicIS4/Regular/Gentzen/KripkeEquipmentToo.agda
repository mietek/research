module BasicIS4.Regular.Gentzen.KripkeEquipmentToo where

open import BasicIS4.Regular.Gentzen public


-- Worlds for the canonical model.

Worldᶜ : Set
Worldᶜ = Cx Ty


-- Not the canonical modal accessibility, based on the 4 axiom.

infix 3 _Яᶜ_
_Яᶜ_ : Worldᶜ → Worldᶜ → Set
w Яᶜ w′ = ∀ {A} → w ⊢ □ A → w′ ⊢ □ □ A

reflЯᶜ : ∀ {w} → w Яᶜ w
reflЯᶜ = up

transЯᶜ : ∀ {w w′ w″} → w Яᶜ w′ → w′ Яᶜ w″ → w Яᶜ w″
transЯᶜ ζ ζ′ = down ∘ ζ′ ∘ ζ

botЯᶜ : ∀ {w} → ⌀ Яᶜ w
botЯᶜ = mono⊢ bot⊆ ∘ up

liftЯᶜ : ∀ {w} → w Яᶜ □⋆ w
liftЯᶜ = down ∘ lift ∘ up


-- Frame conditions given by Božić and Došen, and by Ono.
--
--   zigzag:         zig:
--
--   w′  Я   v′      w′  Я   v′
--   ●───────●       ●───────●
--   │       ┊       │     ⋰
-- ≤ │       ┊ ≤   ≤ │   Я
--   │       ┊       │ ⋰
--   ●╌╌╌╌╌╌╌◌       ●
--   w   Я   v       w

zigЯᶜ : ∀ {v′ w w′} → w′ Яᶜ v′ → w ⊆ w′ → w Яᶜ v′
zigЯᶜ ζ ξ = ζ ∘ mono⊢ ξ

zigzagЯ⨾≤ᶜ : ∀ {v′ w w′} → w′ Яᶜ v′ → w ⊆ w′ → ∃ (λ v → w Яᶜ v × v ⊆ v′)
zigzagЯ⨾≤ᶜ {v′} ζ ξ = v′ , (zigЯᶜ ζ ξ , refl⊆)

infix 3 _Я⨾≤ᶜ_
_Я⨾≤ᶜ_ : Worldᶜ → Worldᶜ → Set
_Я⨾≤ᶜ_ = _Яᶜ_ ⨾ _⊆_

reflЯ⨾≤ᶜ : ∀ {w} → w Я⨾≤ᶜ w
reflЯ⨾≤ᶜ {w} = w , (reflЯᶜ , refl⊆)

transЯ⨾≤ᶜ : ∀ {w w′ w″} → w Я⨾≤ᶜ w′ → w′ Я⨾≤ᶜ w″ → w Я⨾≤ᶜ w″
transЯ⨾≤ᶜ (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) = let v″ , (ζ″ , ξ″) = zigzagЯ⨾≤ᶜ ζ′ ξ
                                           in  v″ , (transЯᶜ ζ ζ″ , trans⊆ ξ″ ξ′)


-- Frame condition given by Ewald et al. and Alechina et al., and a simplified condition.
--
--   zagzig:         zag:
--
--   w′  Я   v′              v′
--   ◌╌╌╌╌╌╌╌●               ●
--   ┊       │             ⋰ ┊
-- ≤ ┊       │ ≤         Я   ┊ ≤
--   ┊       │         ⋰     ┊
--   ●───────●       ●───────●
--   w   Я   v       w   Я   v

zagЯᶜ : ∀ {w v v′} → v ⊆ v′ → w Яᶜ v → w Яᶜ v′
zagЯᶜ {w} ξ ζ = mono⊢ ξ ∘ ζ

zagzig≤⨾Яᶜ : ∀ {w v v′} → v ⊆ v′ → w Яᶜ v → ∃ (λ w′ → w ⊆ w′ × w′ Яᶜ v′)
zagzig≤⨾Яᶜ {w} ξ ζ = w , (refl⊆ , zagЯᶜ ξ ζ)

infix 3 _≤⨾Яᶜ_
_≤⨾Яᶜ_ : Worldᶜ → Worldᶜ → Set
_≤⨾Яᶜ_ = _⊆_ ⨾ _Яᶜ_

refl≤⨾Яᶜ : ∀ {w} → w ≤⨾Яᶜ w
refl≤⨾Яᶜ {w} = w , (refl⊆ , reflЯᶜ)

trans≤⨾Яᶜ : ∀ {w w′ w″} → w ≤⨾Яᶜ w′ → w′ ≤⨾Яᶜ w″ → w ≤⨾Яᶜ w″
trans≤⨾Яᶜ (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) = let v″ , (ξ″ , ζ″) = zagzig≤⨾Яᶜ ξ′ ζ
                                           in  v″ , (trans⊆ ξ ξ″ , transЯᶜ ζ″ ζ′)


-- Frame condition given by Ewald et al., and a dual condition.
--
--   zap:            zup:
--
--   w′  Я   v′      w′  Я   v′
--   ●╌╌╌╌╌╌╌◌       ●───────●
--   │       ┊       ┊       │
-- ≤ │       ┊ ≤   ≤ ┊       │ ≤
--   │       ┊       ┊       │
--   ●───────●       ◌╌╌╌╌╌╌╌●
--   w   Я   v       w   Я   v

-- NOTE: This could be a more precise supremum.
zapЯᶜ : ∀ {v w′ w} → w Яᶜ v → w ⊆ w′ → ∃ (λ v′ → w′ Яᶜ v′ × v ⊆ v′)
zapЯᶜ {v} {w′} ζ ξ = (w′ ⧺ v) , (mono⊢ (weak⊆⧺ₗ v) ∘ up , weak⊆⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupЯᶜ : ∀ {w′ v v′} → v ⊆ v′ → w′ Яᶜ v′ → ∃ (λ w → w ⊆ w′ × w Яᶜ v)
zupЯᶜ ξ ζ = ⌀ , (bot⊆ , botЯᶜ)
