module BasicIS4.DualContext.Gentzen.KripkeEquipment where

open import BasicIS4.DualContext.Gentzen public


-- Worlds for the canonical model.

Worldᶜ : Set
Worldᶜ = Cx² Ty


-- The canonical modal accessibility, based on the T axiom.

infix 3 _Rᶜ_
_Rᶜ_ : Worldᶜ → Worldᶜ → Set
(Γ , Δ) Rᶜ (Γ′ , Δ′) = ∀ {A} → Γ ⁏ Δ ⊢ □ A → Γ′ ⁏ Δ′ ⊢ A

reflRᶜ : ∀ {w} → w Rᶜ w
reflRᶜ = down

transRᶜ : ∀ {w w′ w″} → w Rᶜ w′ → w′ Rᶜ w″ → w Rᶜ w″
transRᶜ ζ ζ′ = ζ′ ∘ ζ ∘ up

botRᶜ : ∀ {w} → ⌀² Rᶜ w
botRᶜ = mono²⊢ bot⊆² ∘ down

liftRᶜ : ∀ {Γ Δ} → (Γ , Δ) Rᶜ (□⋆ Γ , Δ)
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

zigRᶜ : ∀ {v′ w w′} → w′ Rᶜ v′ → w ⊆² w′ → w Rᶜ v′
zigRᶜ ζ ξ = ζ ∘ mono²⊢ ξ

zigzagR⨾⊆² : ∀ {v′ w w′} → w′ Rᶜ v′ → w ⊆² w′ → ∃ (λ v → w Rᶜ v × v ⊆² v′)
zigzagR⨾⊆² {v′} ζ ξ = v′ , (zigRᶜ ζ ξ , refl⊆²)

infix 3 _R⨾⊆²_
_R⨾⊆²_ : Worldᶜ → Worldᶜ → Set
_R⨾⊆²_ = _Rᶜ_ ⨾ _⊆²_

reflR⨾⊆² : ∀ {w} → w R⨾⊆² w
reflR⨾⊆² {w} = w , (reflRᶜ , refl⊆²)

transR⨾⊆² : ∀ {w w′ w″} → w R⨾⊆² w′ → w′ R⨾⊆² w″ → w R⨾⊆² w″
transR⨾⊆² (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) =
  let v″ , (ζ″ , ξ″) = zigzagR⨾⊆² ζ′ ξ
  in  v″ , (transRᶜ ζ ζ″ , trans⊆² ξ″ ξ′)


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

zagRᶜ : ∀ {w v v′} → v ⊆² v′ → w Rᶜ v → w Rᶜ v′
zagRᶜ {w} ξ ζ = mono²⊢ ξ ∘ ζ

zagzig≤⨾Rᶜ : ∀ {w v v′} → v ⊆² v′ → w Rᶜ v → ∃ (λ w′ → w ⊆² w′ × w′ Rᶜ v′)
zagzig≤⨾Rᶜ {w} ξ ζ = w , (refl⊆² , zagRᶜ ξ ζ)

infix 3 _≤⨾Rᶜ_
_≤⨾Rᶜ_ : Worldᶜ → Worldᶜ → Set
_≤⨾Rᶜ_ = _⊆²_ ⨾ _Rᶜ_

refl≤⨾Rᶜ : ∀ {w} → w ≤⨾Rᶜ w
refl≤⨾Rᶜ {w} = w , (refl⊆² , reflRᶜ)

trans≤⨾Rᶜ : ∀ {w w′ w″} → w ≤⨾Rᶜ w′ → w′ ≤⨾Rᶜ w″ → w ≤⨾Rᶜ w″
trans≤⨾Rᶜ (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
  let v″ , (ξ″ , ζ″) = zagzig≤⨾Rᶜ ξ′ ζ
  in  v″ , (trans⊆² ξ ξ″ , transRᶜ ζ″ ζ′)


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
zapRᶜ : ∀ {v w′ w} → w Rᶜ v → w ⊆² w′ → ∃ (λ v′ → w′ Rᶜ v′ × v ⊆² v′)
zapRᶜ {Γ′ , Δ′} {Γ , Δ} ζ ξ =
  (Γ ⧺ Γ′ , Δ ⧺ Δ′) , (mono²⊢ (weak⊆²⧺ₗ (Γ′ , Δ′)) ∘ down , weak⊆²⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupRᶜ : ∀ {w′ v v′} → v ⊆² v′ → w′ Rᶜ v′ → ∃ (λ w → w ⊆² w′ × w Rᶜ v)
zupRᶜ ξ ζ = ⌀² , (bot⊆² , botRᶜ)
