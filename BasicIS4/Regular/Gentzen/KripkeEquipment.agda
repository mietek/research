module BasicIS4.Regular.Gentzen.KripkeEquipment where

open import BasicIS4.Regular.Gentzen


-- The canonical modal accessibility, based on the T axiom.

infix 3 _Rᶜ_
_Rᶜ_ : Cx Ty → Cx Ty → Set
Γ Rᶜ Γ′ = ∀ {A} → Γ ⊢ □ A → Γ′ ⊢ A

reflRᶜ : ∀ {Γ} → Γ Rᶜ Γ
reflRᶜ = down

transRᶜ : ∀ {Γ Γ′ Γ″} → Γ Rᶜ Γ′ → Γ′ Rᶜ Γ″ → Γ Rᶜ Γ″
transRᶜ ζ ζ′ = ζ′ ∘ ζ ∘ up

botRᶜ : ∀ {Γ} → ⌀ Rᶜ Γ
botRᶜ t = mono⊢ bot⊆ (down t)

liftRᶜ : ∀ {Γ} → Γ Rᶜ □⋆ Γ
liftRᶜ {⌀}     t = down t
liftRᶜ {Γ , B} t = down (lift (down t))


-- Frame conditions given by Božić and Došen, and by Ono.
--
-- zigzag         zig
--   Γ′ Rᶜ  Π′      Γ′ Rᶜ  Π′
--   ●──────●       ●──────●
--   │      ┊       │    ⋰
-- ⊆ │      ┊ ⊆   ⊆ │  Rᶜ
--   │      ┊       │ ⋰
--   ●╌╌╌╌╌╌◌       ●
--   Γ  Rᶜ  Π       Γ

zigRᶜ : ∀ {Π′ Γ Γ′} → Γ′ Rᶜ Π′ → Γ ⊆ Γ′ → Γ Rᶜ Π′
zigRᶜ ζ η = ζ ∘ mono⊢ η

zigzagRᶜ⨾⊆ : ∀ {Π′ Γ Γ′} → Γ′ Rᶜ Π′ → Γ ⊆ Γ′ → ∃ (λ Π → Γ Rᶜ Π × Π ⊆ Π′)
zigzagRᶜ⨾⊆ {Π′} ζ η = Π′ , (zigRᶜ ζ η , refl⊆)

infix 3 _Rᶜ⨾⊆_
_Rᶜ⨾⊆_ : Cx Ty → Cx Ty → Set
_Rᶜ⨾⊆_ = _Rᶜ_ ⨾ _⊆_

reflRᶜ⨾⊆ : ∀ {Γ} → Γ Rᶜ⨾⊆ Γ
reflRᶜ⨾⊆ {Γ} = Γ , (reflRᶜ , refl⊆)

transRᶜ⨾⊆ : ∀ {Γ Γ′ Γ″} → Γ Rᶜ⨾⊆ Γ′ → Γ′ Rᶜ⨾⊆ Γ″ → Γ Rᶜ⨾⊆ Γ″
transRᶜ⨾⊆ (a , (ζ , η)) (b , (ζ′ , η′)) = let c , (ζ″ , η″) = zigzagRᶜ⨾⊆ ζ′ η
                                          in  c , (transRᶜ ζ ζ″ , trans⊆ η″ η′)


-- Frame condition given by Ewald et al. and Alechina et al, and a simplified condition.
--
-- zagzig         zag
--   Γ′ Rᶜ  Π′             Π′
--   ◌╌╌╌╌╌╌●              ●
--   ┊      │            ⋰ ┊
-- ⊆ ┊      │ ⊆        Rᶜ  ┊ ⊆
--   ┊      │         ⋰    ┊
--   ●──────●       ●──────●
--   Γ  Rᶜ  Π       Γ  Rᶜ  Π

zagRᶜ : ∀ {Γ Π Π′} → Π ⊆ Π′ → Γ Rᶜ Π → Γ Rᶜ Π′
zagRᶜ {Γ} η ζ = mono⊢ η ∘ ζ

zagzig⊆⨾Rᶜ : ∀ {Γ Π Π′} → Π ⊆ Π′ → Γ Rᶜ Π → ∃ (λ Γ′ → Γ ⊆ Γ′ × Γ′ Rᶜ Π′)
zagzig⊆⨾Rᶜ {Γ} η ζ = Γ , (refl⊆ , zagRᶜ η ζ)

infix 3 _⊆⨾Rᶜ_
_⊆⨾Rᶜ_ : Cx Ty → Cx Ty → Set
_⊆⨾Rᶜ_ = _⊆_ ⨾ _Rᶜ_

refl⊆⨾Rᶜ : ∀ {Γ} → Γ ⊆⨾Rᶜ Γ
refl⊆⨾Rᶜ {Γ} = Γ , (refl⊆ , reflRᶜ)

trans⊆⨾Rᶜ : ∀ {Γ Γ′ Γ″} → Γ ⊆⨾Rᶜ Γ′ → Γ′ ⊆⨾Rᶜ Γ″ → Γ ⊆⨾Rᶜ Γ″
trans⊆⨾Rᶜ (a , (η , ζ)) (b , (η′ , ζ′)) = let c , (η″ , ζ″) = zagzig⊆⨾Rᶜ η′ ζ
                                          in  c , (trans⊆ η η″ , transRᶜ ζ″ ζ′)


-- Frame condition given by Ewald et al., and a dual condition.
--
-- zap            zup
--   Γ′ Rᶜ  Π′      Γ′ Rᶜ  Π′
--   ●╌╌╌╌╌╌◌       ●──────●
--   │      ┊       ┊      │
-- ⊆ │      ┊ ⊆   ⊆ ┊      │ ⊆
--   │      ┊       ┊      │
--   ●──────●       ◌╌╌╌╌╌╌●
--   Γ  Rᶜ  Π       Γ  Rᶜ  Π

-- NOTE: This could be a more precise supremum.
zapRᶜ : ∀ {Π Γ′ Γ} → Γ Rᶜ Π → Γ ⊆ Γ′ → ∃ (λ Π′ → Γ′ Rᶜ Π′ × Π ⊆ Π′)
zapRᶜ {Π} {Γ′} ζ η = (Γ′ ⧺ Π) , ((λ t → mono⊢ (weak⊆⧺ₗ Π) (down t)) , weak⊆⧺ᵣ)

-- NOTE: This could be a more precise infimum.
zupRᶜ : ∀ {Γ′ Π Π′} → Π ⊆ Π′ → Γ′ Rᶜ Π′ → ∃ (λ Γ → Γ ⊆ Γ′ × Γ Rᶜ Π)
zupRᶜ η ζ = ⌀ , (bot⊆ , botRᶜ)
