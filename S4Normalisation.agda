module S4Normalisation where

open import Prelude
open import Category
open import List
open List²
open import ListLemmas
open import AllList
open import S4Propositions
open import S4Derivations
open import S4BidirectionalDerivationsForNormalisation


--------------------------------------------------------------------------------


record Model : Set₁
  where
    field
      World : Set

      -- TODO: Better name
      Ground : World → String → Set

      -- TODO: Better name
      Explode : World → Prop → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {P W W′} → W′ ≥ W → Ground W P
                        → Ground W′ P

      ⌊_⌋₁ : World → List Prop

      ⌊_⌋≥₁ : ∀ {W W′} → W′ ≥ W
                       → ⌊ W′ ⌋₁ ⊇ ⌊ W ⌋₁

open Model {{...}}


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_value
  _⊩_value : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ ι P value   = Ground W P
  W ⊩ A ⊃ B value = ∀ {W′} → W′ ≥ W → W′ ⊩ A thunk
                            → W′ ⊩ B thunk
  W ⊩ □ A value   = W ⊩ A chunk

  infix 3 _⊩_thunk
  _⊩_thunk : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ A thunk = ∀ {B W′} → W′ ≥ W → (∀ {W″} → W″ ≥ W′ → W″ ⊩ A value
                                               → Explode W″ B)
                          → Explode W′ B

  infix 3 _⊩_chunk
  _⊩_chunk : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ A chunk = ⌊ W ⌋₁ ⊢ A valid × W ⊩ A thunk


infix 3 _⊩_allthunk
_⊩_allthunk : ∀ {{_ : Model}} → World → List Prop → Set
W ⊩ Γ allthunk = All (W ⊩_thunk) Γ


infix 3 _⊩_allchunk
_⊩_allchunk : ∀ {{_ : Model}} → World → List Prop → Set
W ⊩ Δ allchunk = All (W ⊩_chunk) Δ


--------------------------------------------------------------------------------


syn : ∀ {{_ : Model}} {A W} → W ⊩ A chunk
                            → ⌊ W ⌋₁ ⊢ A valid
syn v = proj₁ v


syns : ∀ {{_ : Model}} {Δ W} → W ⊩ Δ allchunk
                             → ⌊ W ⌋₁ ⊢ Δ allvalid
syns δ = maps syn δ


sem : ∀ {{_ : Model}} {A W} → W ⊩ A chunk
                            → W ⊩ A thunk
sem v = proj₂ v


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A value
                                 → W′ ⊩ A value
  rel {ι P}   η 𝒟 = relG η 𝒟
  rel {A ⊃ B} η f = \ η′ k → f (η ∘≥ η′) k
  rel {□ A}   η v = relₖ₁ η v

  relₖ : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A thunk
                                  → W′ ⊩ A thunk
  relₖ η k = \ η′ f → k (η ∘≥ η′) f

  relₖ₁ : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A chunk
                                   → W′ ⊩ A chunk
  relₖ₁ {A} η v = mren ⌊ η ⌋≥₁ (syn v) , relₖ {A} η (sem v)


relsₖ : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊩ Γ allthunk
                                 → W′ ⊩ Γ allthunk
relsₖ η γ = maps (\ {A} k {B} {W′} → relₖ {A} η (\ {C} {W″} → k {C} {W″})) γ
-- NOTE: Pattern-matching problem here prevents rel from taking “A true”
-- NOTE: Equivalent to
-- relsₖ η γ = maps (relₖ η) γ


relsₖ₁ : ∀ {{_ : Model}} {Δ W W′} → W′ ≥ W → W ⊩ Δ allchunk
                                  → W′ ⊩ Δ allchunk
relsₖ₁ η δ = maps (relₖ₁ η) δ


--------------------------------------------------------------------------------


return : ∀ {{_ : Model}} {A W} → W ⊩ A value
                               → W ⊩ A thunk
return {A} a = \ η f → f id≥ (rel {A} η a)


bind : ∀ {{_ : Model}} {A B W} → W ⊩ A thunk → (∀ {W′} → W′ ≥ W → W′ ⊩ A value
                                                          → W′ ⊩ B thunk)
                               → W ⊩ B thunk
bind k f = \ η f′ →
             k η (\ η′ a →
               f (η ∘≥ η′) a id≥ (\ η″ b →
                 f′ (η′ ∘≥ η″) b))


--------------------------------------------------------------------------------


infix 3 _⊨_true
_⊨_true : List² Prop Prop → Prop → Set₁
Δ ⨾ Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩ Δ allchunk → W ⊩ Γ allthunk
                                      → W ⊩ A thunk


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊨ A true
↓ (var i)              δ γ = get γ i
↓ (lam {A} {B} 𝒟)      δ γ = return {A ⊃ B} (\ η k →
                               ↓ 𝒟 (relsₖ₁ η δ) (relsₖ η γ , k))
↓ (app {A} {B} 𝒟 ℰ)    δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                               f id≥ (↓ ℰ (relsₖ₁ η δ) (relsₖ η γ)))
↓ (mvar i)             δ γ = sem (get δ i)
↓ (box {A} 𝒟)          δ γ = return {□ A} (msub (syns δ) 𝒟 , ↓ 𝒟 δ ∙)
↓ (letbox {A} {B} 𝒟 ℰ) δ γ = bind {□ A} {B} (↓ 𝒟 δ γ) (\ η v →
                               ↓ ℰ (relsₖ₁ η δ , v) (relsₖ η γ))


--------------------------------------------------------------------------------


renᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ A usable
                        → Δ′ ⨾ Γ′ ⊢ A usable
renᵣ² η 𝒟 = mrenᵣ (proj₁ η) (renᵣ (proj₂ η) 𝒟)


instance
  canon : Model
  canon = record
            { World   = List² Prop Prop
            ; Ground  = \ { (Δ ⨾ Γ) P → Δ ⨾ Γ ⊢ ι P usable }
            ; Explode = \ { (Δ ⨾ Γ) A → Δ ⨾ Γ ⊢ A verifiable }
            ; _≥_     = _⊇²_
            ; id≥     = id
            ; _∘≥_    = _∘_
            ; relG    = renᵣ²
            ; ⌊_⌋₁    = proj₁
            ; ⌊_⌋≥₁   = proj₁
            }


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ A usable
                → Δ ⨾ Γ ⊩ A thunk
  ⇓ {ι P}   𝒟 = return {ι P} 𝒟
  ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renᵣ² η 𝒟) (⇑ k)))
  ⇓ {□ A}   𝒟 = \ η f → letbox (renᵣ² η 𝒟) (f (drop₁ id) (mvz , ⇓ mvzᵣ))

  ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊩ A thunk
                → Δ ⨾ Γ ⊢ A verifiable
  ⇑ {ι P}   k = k id (\ η 𝒟 → use 𝒟)
  ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzᵣ))))
  ⇑ {□ A}   k = k id (\ η v → box (syn v))


--------------------------------------------------------------------------------


wksₛ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allthunk
                   → Δ ⨾ Γ , A ⊩ Ξ allthunk
wksₛ ξ = relsₖ (drop₂ id) ξ


liftsₛ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allthunk
                     → Δ ⨾ Γ , A ⊩ Ξ , A allthunk
liftsₛ ξ = wksₛ ξ , ⇓ vzᵣ


varsₛ : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                   → Δ ⨾ Γ′ ⊩ Γ allthunk
varsₛ done     = ∙
varsₛ (drop η) = wksₛ (varsₛ η)
varsₛ (keep η) = liftsₛ (varsₛ η)


idsₛ : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Γ allthunk
idsₛ = varsₛ id


--------------------------------------------------------------------------------


mwksₛ₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allchunk
                     → Δ , A ⨾ Γ ⊩ Ξ allchunk
mwksₛ₁ ξ = relsₖ₁ (drop₁ id) ξ


mliftsₛ₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allchunk
                       → Δ , A ⨾ Γ ⊩ Ξ , A allchunk
mliftsₛ₁ ξ = mwksₛ₁ ξ , (mvz , ⇓ mvzᵣ)


mvarsₛ₁ : ∀ {Δ Δ′ Γ} → Δ′ ⊇ Δ
                     → Δ′ ⨾ Γ ⊩ Δ allchunk
mvarsₛ₁ done     = ∙
mvarsₛ₁ (drop η) = mwksₛ₁ (mvarsₛ₁ η)
mvarsₛ₁ (keep η) = mliftsₛ₁ (mvarsₛ₁ η)


midsₛ₁ : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Δ allchunk
midsₛ₁ = mvarsₛ₁ id


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊨ A true
              → Δ ⨾ Γ ⊢ A verifiable
↑ f = ⇑ (f midsₛ₁ idsₛ)


nbe : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ Γ ⊢ A verifiable
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
