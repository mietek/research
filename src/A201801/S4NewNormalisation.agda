{-# OPTIONS --rewriting #-}

module A201801.S4NewNormalisation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open List²
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.S4Propositions
open import A201801.S4StandardDerivations
open import A201801.S4NewBidirectionalDerivationsForNormalisation
import A201801.S4EmbeddingOfIPL as OfIPL
import A201801.S4ProjectionToIPL as ToIPL
import A201801.IPLPropositions as IPL
import A201801.IPLStandardDerivations as IPL


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

--      peek : World → List Assert
--
--      peek≥ : ∀ {W W′} → W′ ≥ W
--                       → peek W′ ⊇ peek W

open Model {{...}}


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_value
  _⊩_value : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ ι P value   = Ground W P
  W ⊩ A ⊃ B value = ∀ {W′ : World} → W′ ≥ W → W′ ⊩ A thunk
                                    → W′ ⊩ B thunk
  W ⊩ □ A value   = W ⊩ ⟪⊫ A ⟫ chunk

  infix 3 _⊩_thunk
  _⊩_thunk : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ A thunk = ∀ {B} {W′ : World} → W′ ≥ W → (∀ {W″ : World} → W″ ≥ W′ → W″ ⊩ A value
                                                                 → Explode W″ B)
                                    → Explode W′ B

  infix 3 _⊩_chunk
  _⊩_chunk : ∀ {{_ : Model}} → World → Assert → Set
  W ⊩ ⟪⊫ A ⟫ chunk = ∙ IPL.⊢ ToIPL.↓ₚ A true × W ⊩ A thunk


infix 3 _⊩_allthunk
_⊩_allthunk : ∀ {{_ : Model}} → World → List Form → Set
W ⊩ Γ allthunk = All (W ⊩_thunk) Γ


infix 3 _⊩_allchunk
_⊩_allchunk : ∀ {{_ : Model}} → World → List Assert → Set
W ⊩ Δ allchunk = All (W ⊩_chunk) Δ


--------------------------------------------------------------------------------


syn : ∀ {{_ : Model}} {A} {W : World} → W ⊩ ⟪⊫ A ⟫ chunk
                                      → ∙ IPL.⊢ ToIPL.↓ₚ A true
syn (𝒟 , k) = 𝒟


syns : ∀ {{_ : Model}} {Δ} {W : World} → W ⊩ Δ allchunk
                                       → ∙ IPL.⊢ ToIPL.↓ₐₛ Δ alltrue
syns ∙                       = ∙
syns (_,_ {A = ⟪⊫ A ⟫} δ c) = syns δ , syn {A} c


sem : ∀ {{_ : Model}} {A} {W : World} → W ⊩ ⟪⊫ A ⟫ chunk
                                      → W ⊩ A thunk
sem (𝒟 , k) = k


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A value
                                           → W′ ⊩ A value
  rel {ι P}   η 𝒟 = relG η 𝒟
  rel {A ⊃ B} η f = \ η′ k → f (η ∘≥ η′) k
  rel {□ A}   η c = chrel {⟪⊫ A ⟫} η c

  threl : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A thunk
                                             → W′ ⊩ A thunk
  threl η k = \ η′ f → k (η ∘≥ η′) f

  chrel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A chunk
                                             → W′ ⊩ A chunk
  chrel {⟪⊫ A ⟫} η c = syn {A} c , threl {A} η (sem {A} c)


threls : ∀ {{_ : Model}} {Γ} {W W′ : World} → W′ ≥ W → W ⊩ Γ allthunk
                                            → W′ ⊩ Γ allthunk
threls η γ = maps (\ {A} k {B} {W′} → threl {A} η (\ {C} {W″} → k {C} {W″})) γ  -- NOTE: Annoying


chrels : ∀ {{_ : Model}} {Δ} {W W′ : World} → W′ ≥ W → W ⊩ Δ allchunk
                                            → W′ ⊩ Δ allchunk
chrels η δ = maps (\ { {⟪⊫ A ⟫} c → chrel {⟪⊫ A ⟫} η c }) δ


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


infix 3 _⊨_valid[_]
_⊨_valid[_] : List Assert → Form → List Form → Set₁
Δ ⊨ A valid[ Γ ] = ∀ {{_ : Model}} {W : World} → W ⊩ Δ allchunk → W ⊩ Γ allthunk
                                                → W ⊩ A thunk


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ ⊨ A valid[ Γ ]
↓ (var i)              δ γ = get γ i
↓ (lam {A} {B} 𝒟)      δ γ = return {A ⊃ B} (\ η k →
                               ↓ 𝒟 (chrels η δ) (threls η γ , k))
↓ (app {A} {B} 𝒟 ℰ)    δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                               f id≥ (↓ ℰ (chrels η δ) (threls η γ)))
↓ (mvar {A} i)         δ γ = sem {A} (get δ i)
↓ (box {A} 𝒟)          δ γ = return {□ A} (IPL.sub (syns δ) (ToIPL.↓ 𝒟) , ↓ 𝒟 δ ∙)
↓ (letbox {A} {B} 𝒟 ℰ) δ γ = bind {□ A} {B} (↓ 𝒟 δ γ) (\ η c →
                               ↓ ℰ (chrels η δ , c) (threls η γ))


--------------------------------------------------------------------------------


ren² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⊢ A neutral[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ′ ]
ren² (η₁ , η₂) 𝒟 = mrenᵣ η₁ (renᵣ η₂ 𝒟)


instance
  canon : Model
  canon = record
            { World   = List² Assert Form
            ; Ground  = \ { (Δ ⨾ Γ) P → Δ ⊢ ι P neutral[ Γ ] }
            ; Explode = \ { (Δ ⨾ Γ) A → Δ ⊢ A normal[ Γ ] }
            ; _≥_     = _⊇²_
            ; id≥     = id
            ; _∘≥_    = _∘_
            ; relG    = ren²
            }


-- TODO: unfinished
-- mutual
--   ⇓ : ∀ {A Δ Γ} → Δ ⊢ A neutral[ Γ ]
--                 → Δ ⨾ Γ ⊩ A thunk
--   ⇓ {ι P}   𝒟 = return {ι P} 𝒟
--   ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (ren² η 𝒟) (⇑ k)))
--   ⇓ {□ A}   𝒟 = \ η f → {!!}
--   -- letbox (ren² η 𝒟) (f (drop₁ id) (mvz , ⇓ mvzᵣ))

--   ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊩ A thunk
--                 → Δ ⊢ A normal[ Γ ]
--   ⇑ {ι P}   k = k id (\ η 𝒟 → use 𝒟)
--   ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzᵣ))))
--   ⇑ {□ A}   k = k id (\ η c → {!box (syn {A} c)!})  -- OfIPL.↑ₚ (ToIPL.↓ₚ A) != A


-- --------------------------------------------------------------------------------


-- swks : ∀ {A : Form} {Δ : List Assert} {Γ Ξ : List Form} → Δ ⨾ Γ ⊩ Ξ allthunk
--                                                         → Δ ⨾ Γ , A ⊩ Ξ allthunk
-- swks ξ = threls (drop₂ id) ξ


-- slifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allthunk
--                      → Δ ⨾ Γ , A ⊩ Ξ , A allthunk
-- slifts ξ = swks ξ , ⇓ vzᵣ


-- svars : ∀ {Δ : List Assert} {Γ Γ′} → Γ′ ⊇ Γ
--                                    → Δ ⨾ Γ′ ⊩ Γ allthunk
-- svars done     = ∙
-- svars (drop η) = swks (svars η)
-- svars (keep η) = slifts (svars η)


-- sids : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Γ allthunk
-- sids = svars id


-- --------------------------------------------------------------------------------


-- smwks : ∀ {A : Assert} {Δ Ξ : List Assert} {Γ : List Form} → Δ ⨾ Γ ⊩ Ξ allchunk
--                                                            → Δ , A ⨾ Γ ⊩ Ξ allchunk
-- smwks ξ = chrels (drop₁ id) ξ


-- -- TODO: unfinished
-- -- smlifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allchunk
-- --                       → Δ , A ⨾ Γ ⊩ Ξ , A allchunk
-- -- smlifts ξ = {!!} -- smwks ξ , (mvz , ⇓ mvzᵣ)


-- -- smvars : ∀ {Δ Δ′} {Γ : List Form} → Δ′ ⊇ Δ
-- --                                   → Δ′ ⨾ Γ ⊩ Δ allchunk
-- -- smvars done     = ∙
-- -- smvars (drop η) = smwks (smvars η)
-- -- smvars (keep η) = smlifts (smvars η)


-- -- smids : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Δ allchunk
-- -- smids = smvars id


-- -- --------------------------------------------------------------------------------


-- -- ↑ : ∀ {Δ Γ A} → Δ ⊨ A valid[ Γ ]
-- --               → Δ ⊢ A normal[ Γ ]
-- -- ↑ f = ⇑ (f smids sids)


-- -- nm : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
-- --                → Δ ⊢ A normal[ Γ ]
-- -- nm 𝒟 = ↑ (↓ 𝒟)


-- -- --------------------------------------------------------------------------------
