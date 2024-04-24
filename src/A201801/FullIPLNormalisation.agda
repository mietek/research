module A201801.FullIPLNormalisation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions
open import A201801.FullIPLDerivations
open import A201801.FullIPLBidirectionalDerivationsForNormalisation


--------------------------------------------------------------------------------


record Model : Set₁
  where
    field
      World : Set

      -- TODO: Better name
      Ground : World → String → Set

      -- TODO: Better name
      Explode : World → Form → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {P W W′} → W′ ≥ W → Ground W P
                        → Ground W′ P

open Model {{...}} public


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_value
  _⊩_value : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ ι P value   = Ground W P
  W ⊩ A ⊃ B value = ∀ {W′ : World} → W′ ≥ W → W′ ⊩ A thunk
                                    → W′ ⊩ B thunk
  W ⊩ A ∧ B value = W ⊩ A thunk × W ⊩ B thunk
  W ⊩ 𝟙 value     = ⊤
  W ⊩ 𝟘 value     = ⊥
  W ⊩ A ∨ B value = W ⊩ A thunk ⊎ W ⊩ B thunk

  infix 3 _⊩_thunk
  _⊩_thunk : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ A thunk = ∀ {B} {W′ : World} → W′ ≥ W → (∀ {W″ : World} → W″ ≥ W′ → W″ ⊩ A value
                                                                 → Explode W″ B)
                                    → Explode W′ B


infix 3 _⊩_allthunk
_⊩_allthunk : ∀ {{_ : Model}} → World → List Form → Set
W ⊩ Γ allthunk = All (W ⊩_thunk) Γ


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A value
                                           → W′ ⊩ A value
  rel {ι P}   η 𝒟         = relG η 𝒟
  rel {A ⊃ B} η f         = \ η′ k → f (η ∘≥ η′) k
  rel {A ∧ B} η (k₁ , k₂) = threl {A} η k₁ , threl {B} η k₂
  rel {𝟙}     η ∙         = ∙
  rel {𝟘}     η ()
  rel {A ∨ B} η (inj₁ k₁) = inj₁ (threl {A} η k₁)
  rel {A ∨ B} η (inj₂ k₂) = inj₂ (threl {B} η k₂)

  threl : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A thunk
                                             → W′ ⊩ A thunk
  threl η k = \ η′ f → k (η ∘≥ η′) f


threls : ∀ {{_ : Model}} {Γ} {W W′ : World} → W′ ≥ W → W ⊩ Γ allthunk
                                            → W′ ⊩ Γ allthunk
threls η γ = maps (\ {A} k {B} {W′} → threl {A} η (\ {C} {W″} → k {C} {W″})) γ  -- NOTE: Annoying


--------------------------------------------------------------------------------


return : ∀ {{_ : Model}} {A} {W : World} → W ⊩ A value
                                         → W ⊩ A thunk
return {A} a = \ η f → f id≥ (rel {A} η a)


bind : ∀ {{_ : Model}} {A B} {W : World} → W ⊩ A thunk → (∀ {W′ : World} → W′ ≥ W → W′ ⊩ A value
                                                                            → W′ ⊩ B thunk)
                                         → W ⊩ B thunk
bind k f = \ η f′ →
             k η (\ η′ a →
               f (η ∘≥ η′) a id≥ (\ η″ b →
                 f′ (η′ ∘≥ η″) b))


--------------------------------------------------------------------------------


infix 3 _⊨_true
_⊨_true : List Form → Form → Set₁
Γ ⊨ A true = ∀ {{_ : Model}} {W : World} → W ⊩ Γ allthunk
                                          → W ⊩ A thunk


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var i)                  γ = get γ i
↓ (lam {A} {B} 𝒟)          γ = return {A ⊃ B} (\ η k →
                                 ↓ 𝒟 (threls η γ , k))
↓ (app {A} {B} 𝒟 ℰ)        γ = bind {A ⊃ B} {B} (↓ 𝒟 γ) (\ η f →
                                 f id≥ (↓ ℰ (threls η γ)))
↓ (pair {A} {B} 𝒟 ℰ)       γ = return {A ∧ B} (↓ 𝒟 γ , ↓ ℰ γ)
↓ (fst {A} {B} 𝒟)          γ = bind {A ∧ B} {A} (↓ 𝒟 γ) (\ { η (k₁ , k₂) → k₁ })
↓ (snd {A} {B} 𝒟)          γ = bind {A ∧ B} {B} (↓ 𝒟 γ) (\ { η (k₁ , k₂) → k₂ })
↓ unit                     γ = return {𝟙} ∙
↓ (abort {A} 𝒟)            γ = bind {𝟘} {A} (↓ 𝒟 γ) (\ η ())
↓ (inl {A} {B} 𝒟)          γ = return {A ∨ B} (inj₁ (↓ 𝒟 γ))
↓ (inr {A} {B} 𝒟)          γ = return {A ∨ B} (inj₂ (↓ 𝒟 γ))
↓ (case {A} {B} {C} 𝒟 ℰ ℱ) γ = bind {A ∨ B} {C} (↓ 𝒟 γ) (\ { η (inj₁ k₁) → ↓ ℰ (threls η γ , k₁)
                                                           ; η (inj₂ k₂) → ↓ ℱ (threls η γ , k₂)
                                                           })


--------------------------------------------------------------------------------


private
  instance
    canon : Model
    canon = record
              { World   = List Form
              ; Ground  = \ Γ P → Γ ⊢ ι P neutral
              ; Explode = \ Γ A → Γ ⊢ A normal
              ; _≥_     = _⊇_
              ; id≥     = id
              ; _∘≥_    = _∘_
              ; relG    = renₗ
              }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ A neutral
              → Γ ⊩ A thunk
  ⇓ {ι P}   𝒟 = return {ι P} 𝒟
  ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renₗ η 𝒟) (⇑ k)))
  ⇓ {A ∧ B} 𝒟 = return {A ∧ B} (⇓ (fst 𝒟) , ⇓ (snd 𝒟))
  ⇓ {𝟙}     𝒟 = return {𝟙} ∙
  ⇓ {𝟘}     𝒟 = \ η k → abort (renₗ η 𝒟)
  ⇓ {A ∨ B} 𝒟 = \ η k → case (renₗ η 𝒟)
                              (k (drop id) (inj₁ (⇓ {A} vzₗ)))
                              (k (drop id) (inj₂ (⇓ {B} vzₗ)))

  ⇑ : ∀ {A Γ} → Γ ⊩ A thunk
              → Γ ⊢ A normal
  ⇑ {ι P}   k = k id (\ η 𝒟 → use 𝒟)
  ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop id) (⇓ vzₗ))))
  ⇑ {A ∧ B} k = k id (\ { η (k₁ , k₂) → pair (⇑ k₁) (⇑ k₂) })
  ⇑ {𝟙}     k = k id (\ { η ∙ → unit })
  ⇑ {𝟘}     k = k id (\ { η () })
  ⇑ {A ∨ B} k = k id (\ { η (inj₁ k₁) → inl (⇑ k₁)
                        ; η (inj₂ k₂) → inr (⇑ k₂)
                        })


--------------------------------------------------------------------------------


swks : ∀ {A : Form} {Γ Ξ : List Form} → Γ ⊩ Ξ allthunk
                                      → Γ , A ⊩ Ξ allthunk
swks ξ = threls (drop id) ξ


slifts : ∀ {A Γ Ξ} → Γ ⊩ Ξ allthunk
                   → Γ , A ⊩ Ξ , A allthunk
slifts ξ = swks ξ , ⇓ vzₗ


svars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩ Γ allthunk
svars done     = ∙
svars (drop η) = swks (svars η)
svars (keep η) = slifts (svars η)


sids : ∀ {Γ} → Γ ⊩ Γ allthunk
sids = svars id


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ A normal
↑ f = ⇑ (f sids)


nm : ∀ {Γ A} → Γ ⊢ A true
             → Γ ⊢ A normal
nm 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
