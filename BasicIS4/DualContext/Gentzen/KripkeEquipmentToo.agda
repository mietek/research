module BasicIS4.DualContext.Gentzen.KripkeEquipmentToo where

open import BasicIS4.DualContext.Gentzen public


-- Worlds for the canonical model.

Worldᶜ : Set
Worldᶜ = Cx² Ty


-- Not the canonical modal accessibility, based on the 4 axiom.

infix 3 _Яᶜ_
_Яᶜ_ : Worldᶜ → Worldᶜ → Set
(Γ , Δ) Яᶜ (Γ′ , Δ′) = ∀ {A} → Γ ⁏ Δ ⊢ □ A → Γ′ ⁏ Δ′ ⊢ □ □ A

reflЯᶜ : ∀ {w} → w Яᶜ w
reflЯᶜ = up

transЯᶜ : ∀ {w w′ w″} → w Яᶜ w′ → w′ Яᶜ w″ → w Яᶜ w″
transЯᶜ ζ ζ′ = down ∘ ζ′ ∘ ζ

botЯᶜ : ∀ {w} → ⌀² Яᶜ w
botЯᶜ = mono²⊢ bot⊆² ∘ up

liftЯᶜ : ∀ {Γ Δ} → (Γ , Δ) Яᶜ (□⋆ Γ , Δ)
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

zigЯᶜ : ∀ {v′ w w′} → w′ Яᶜ v′ → w ⊆² w′ → w Яᶜ v′
zigЯᶜ ζ ξ = ζ ∘ mono²⊢ ξ

zigzagЯ⨾⊆² : ∀ {v′ w w′} → w′ Яᶜ v′ → w ⊆² w′ → ∃ (λ v → w Яᶜ v × v ⊆² v′)
zigzagЯ⨾⊆² {v′} ζ ξ = v′ , (zigЯᶜ ζ ξ , refl⊆²)

infix 3 _Я⨾⊆²_
_Я⨾⊆²_ : Worldᶜ → Worldᶜ → Set
_Я⨾⊆²_ = _Яᶜ_ ⨾ _⊆²_

reflЯ⨾⊆² : ∀ {w} → w Я⨾⊆² w
reflЯ⨾⊆² {w} = w , (reflЯᶜ , refl⊆²)

transЯ⨾⊆² : ∀ {w w′ w″} → w Я⨾⊆² w′ → w′ Я⨾⊆² w″ → w Я⨾⊆² w″
transЯ⨾⊆² (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) = let v″ , (ζ″ , ξ″) = zigzagЯ⨾⊆² ζ′ ξ
                                           in  v″ , (transЯᶜ ζ ζ″ , trans⊆² ξ″ ξ′)


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

zagЯᶜ : ∀ {w v v′} → v ⊆² v′ → w Яᶜ v → w Яᶜ v′
zagЯᶜ {w} ξ ζ = mono²⊢ ξ ∘ ζ

zagzig≤⨾Яᶜ : ∀ {w v v′} → v ⊆² v′ → w Яᶜ v → ∃ (λ w′ → w ⊆² w′ × w′ Яᶜ v′)
zagzig≤⨾Яᶜ {w} ξ ζ = w , (refl⊆² , zagЯᶜ ξ ζ)

infix 3 _≤⨾Яᶜ_
_≤⨾Яᶜ_ : Worldᶜ → Worldᶜ → Set
_≤⨾Яᶜ_ = _⊆²_ ⨾ _Яᶜ_

refl≤⨾Яᶜ : ∀ {w} → w ≤⨾Яᶜ w
refl≤⨾Яᶜ {w} = w , (refl⊆² , reflЯᶜ)

trans≤⨾Яᶜ : ∀ {w w′ w″} → w ≤⨾Яᶜ w′ → w′ ≤⨾Яᶜ w″ → w ≤⨾Яᶜ w″
trans≤⨾Яᶜ (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
  let v″ , (ξ″ , ζ″) = zagzig≤⨾Яᶜ ξ′ ζ
  in  v″ , (trans⊆² ξ ξ″ , transЯᶜ ζ″ ζ′)


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
zapЯᶜ : ∀ {v w′ w} → w Яᶜ v → w ⊆² w′ → ∃ (λ v′ → w′ Яᶜ v′ × v ⊆² v′)
zapЯᶜ {Γ′ , Δ′} {Γ , Δ} ζ ξ =
  (Γ ⧺ Γ′ , Δ ⧺ Δ′) , (mono²⊢ (weak⊆²⧺ₗ (Γ′ , Δ′)) ∘ up , weak⊆²⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupЯᶜ : ∀ {w′ v v′} → v ⊆² v′ → w′ Яᶜ v′ → ∃ (λ w → w ⊆² w′ × w Яᶜ v)
zupЯᶜ ξ ζ = ⌀² , (bot⊆² , botЯᶜ)
