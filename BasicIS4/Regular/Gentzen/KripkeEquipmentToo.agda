module BasicIS4.Regular.Gentzen.KripkeEquipmentToo where

open import BasicIS4.Regular.Gentzen


-- Not the canonical modal accessibility, based on the 4 axiom.

infix 3 _Яᶜ_
_Яᶜ_ : Cx Ty → Cx Ty → Set
Γ Яᶜ Γ′ = ∀ {A} → Γ ⊢ □ A → Γ′ ⊢ □ □ A

reflЯᶜ : ∀ {Γ} → Γ Яᶜ Γ
reflЯᶜ = up

transЯᶜ : ∀ {Γ Γ′ Γ″} → Γ Яᶜ Γ′ → Γ′ Яᶜ Γ″ → Γ Яᶜ Γ″
transЯᶜ ζ ζ′ = down ∘ ζ′ ∘ ζ

botЯᶜ : ∀ {Γ} → ⌀ Яᶜ Γ
botЯᶜ t = mono⊢ bot⊆ (up t)

liftЯᶜ : ∀ {Γ} → Γ Яᶜ □⋆ Γ
liftЯᶜ {⌀}     t = up t
liftЯᶜ {Γ , B} t = down (lift (up t))


-- Frame conditions given by Božić and Došen, and by Ono.
--
-- zigzag         zig
--   Γ′ Яᶜ  Π′      Γ′ Яᶜ  Π′
--   ●──────●       ●──────●
--   │      ┊       │    ⋰
-- ⊆ │      ┊ ⊆   ⊆ │  Яᶜ
--   │      ┊       │ ⋰
--   ●╌╌╌╌╌╌◌       ●
--   Γ  Яᶜ  Π       Γ

zigЯᶜ : ∀ {Π′ Γ Γ′} → Γ′ Яᶜ Π′ → Γ ⊆ Γ′ → Γ Яᶜ Π′
zigЯᶜ ζ η = ζ ∘ mono⊢ η

zigzagЯᶜ⨾⊆ : ∀ {Π′ Γ Γ′} → Γ′ Яᶜ Π′ → Γ ⊆ Γ′ → ∃ (λ Π → Γ Яᶜ Π × Π ⊆ Π′)
zigzagЯᶜ⨾⊆ {Π′} ζ η = Π′ , (zigЯᶜ ζ η , refl⊆)

infix 3 _Яᶜ⨾⊆_
_Яᶜ⨾⊆_ : Cx Ty → Cx Ty → Set
_Яᶜ⨾⊆_ = _Яᶜ_ ⨾ _⊆_

reflЯᶜ⨾⊆ : ∀ {Γ} → Γ Яᶜ⨾⊆ Γ
reflЯᶜ⨾⊆ {Γ} = Γ , (reflЯᶜ , refl⊆)

transЯᶜ⨾⊆ : ∀ {Γ Γ′ Γ″} → Γ Яᶜ⨾⊆ Γ′ → Γ′ Яᶜ⨾⊆ Γ″ → Γ Яᶜ⨾⊆ Γ″
transЯᶜ⨾⊆ (a , (ζ , η)) (b , (ζ′ , η′)) = let c , (ζ″ , η″) = zigzagЯᶜ⨾⊆ ζ′ η
                                          in  c , (transЯᶜ ζ ζ″ , trans⊆ η″ η′)


-- Frame condition given by Ewald et al. and Alechina et al, and a simplified condition.
--
-- zagzig         zag
--   Γ′ Яᶜ  Π′             Π′
--   ◌╌╌╌╌╌╌●              ●
--   ┊      │            ⋰ ┊
-- ⊆ ┊      │ ⊆        Яᶜ  ┊ ⊆
--   ┊      │         ⋰    ┊
--   ●──────●       ●──────●
--   Γ  Яᶜ  Π       Γ  Яᶜ  Π

zagЯᶜ : ∀ {Γ Π Π′} → Π ⊆ Π′ → Γ Яᶜ Π → Γ Яᶜ Π′
zagЯᶜ {Γ} η ζ = mono⊢ η ∘ ζ

zagzig⊆⨾Яᶜ : ∀ {Γ Π Π′} → Π ⊆ Π′ → Γ Яᶜ Π → ∃ (λ Γ′ → Γ ⊆ Γ′ × Γ′ Яᶜ Π′)
zagzig⊆⨾Яᶜ {Γ} η ζ = Γ , (refl⊆ , zagЯᶜ η ζ)

infix 3 _⊆⨾Яᶜ_
_⊆⨾Яᶜ_ : Cx Ty → Cx Ty → Set
_⊆⨾Яᶜ_ = _⊆_ ⨾ _Яᶜ_

refl⊆⨾Яᶜ : ∀ {Γ} → Γ ⊆⨾Яᶜ Γ
refl⊆⨾Яᶜ {Γ} = Γ , (refl⊆ , reflЯᶜ)

trans⊆⨾Яᶜ : ∀ {Γ Γ′ Γ″} → Γ ⊆⨾Яᶜ Γ′ → Γ′ ⊆⨾Яᶜ Γ″ → Γ ⊆⨾Яᶜ Γ″
trans⊆⨾Яᶜ (a , (η , ζ)) (b , (η′ , ζ′)) = let c , (η″ , ζ″) = zagzig⊆⨾Яᶜ η′ ζ
                                          in  c , (trans⊆ η η″ , transЯᶜ ζ″ ζ′)


-- Frame condition given by Ewald et al., and a dual condition.
--
-- zap            zup
--   Γ′ Яᶜ  Π′      Γ′ Яᶜ  Π′
--   ●╌╌╌╌╌╌◌       ●──────●
--   │      ┊       ┊      │
-- ⊆ │      ┊ ⊆   ⊆ ┊      │ ⊆
--   │      ┊       ┊      │
--   ●──────●       ◌╌╌╌╌╌╌●
--   Γ  Яᶜ  Π       Γ  Яᶜ  Π

-- NOTE: This could be a more precise supremum.
zapЯᶜ : ∀ {Π Γ′ Γ} → Γ Яᶜ Π → Γ ⊆ Γ′ → ∃ (λ Π′ → Γ′ Яᶜ Π′ × Π ⊆ Π′)
zapЯᶜ {Π} {Γ′} ζ η = (Γ′ ⧺ Π) , ((λ t → mono⊢ (weak⊆⧺ₗ Π) (up t)) , weak⊆⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupЯᶜ : ∀ {Γ′ Π Π′} → Π ⊆ Π′ → Γ′ Яᶜ Π′ → ∃ (λ Γ → Γ ⊆ Γ′ × Γ Яᶜ Π)
zupЯᶜ η ζ = ⌀ , (bot⊆ , botЯᶜ)
