{-# OPTIONS --rewriting #-}

module A201801.CMLStandardNormalisation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open List²
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.CMLPropositions
open import A201801.CMLStandardDerivations
open import A201801.CMLStandardBidirectionalDerivations-NormalNeutral


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

      peek : World → List Assert

      peek≥ : ∀ {W W′} → W′ ≥ W
                       → peek W′ ⊇ peek W

open Model {{...}} public


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_value
  _⊩_value : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ ι P value     = Ground W P
  W ⊩ A ⊃ B value   = ∀ {W′ : World} → W′ ≥ W → W′ ⊩ A thunk
                                      → W′ ⊩ B thunk
  W ⊩ [ Ψ ] A value = W ⊩ ⟪ Ψ ⊫ A ⟫ chunk

  infix 3 _⊩_thunk
  _⊩_thunk : ∀ {{_ : Model}} → World → Form → Set
  W ⊩ A thunk = ∀ {B} {W′ : World} → W′ ≥ W → (∀ {W″ : World} → W″ ≥ W′ → W″ ⊩ A value
                                                                 → Explode W″ B)
                                    → Explode W′ B

  infix 3 _⊩_chunk
  _⊩_chunk : ∀ {{_ : Model}} → World → Assert → Set
  W ⊩ ⟪ Ψ ⊫ A ⟫ chunk = peek W ⊢ A valid[ Ψ ] × (∀ {W′ : World} → W′ ≥ W → W′ ⊩ Ψ allthunk
                                                                   → W′ ⊩ A thunk)

  infix 3 _⊩_allthunk
  _⊩_allthunk : ∀ {{_ : Model}} → World → List Form → Set
  W ⊩ ∙     allthunk = ⊤
  W ⊩ Γ , A allthunk = W ⊩ Γ allthunk × W ⊩ A thunk


infix 3 _⊩_allchunk
_⊩_allchunk : ∀ {{_ : Model}} → World → List Assert → Set
W ⊩ Δ allchunk = All (W ⊩_chunk) Δ


--------------------------------------------------------------------------------


syn : ∀ {{_ : Model}} {A Ψ} {W : World} → W ⊩ ⟪ Ψ ⊫ A ⟫ chunk
                                        → peek W ⊢ A valid[ Ψ ]
syn (𝒟 , k) = 𝒟


syns : ∀ {{_ : Model}} {Δ} {W : World} → W ⊩ Δ allchunk
                                       → peek W ⊢ Δ allvalid*
syns δ = maps syn δ


sem : ∀ {{_ : Model}} {A Ψ} {W : World} → W ⊩ ⟪ Ψ ⊫ A ⟫ chunk
                                        → (∀ {W′} → W′ ≥ W → W′ ⊩ Ψ allthunk
                                                   → W′ ⊩ A thunk)
sem (𝒟 , k) = k


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A value
                                           → W′ ⊩ A value
  rel {ι P}     η 𝒟 = relG η 𝒟
  rel {A ⊃ B}   η f = \ η′ k → f (η ∘≥ η′) k
  rel {[ Ψ ] A} η f = chrel η f

  threl : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A thunk
                                             → W′ ⊩ A thunk
  threl η k = \ η′ f → k (η ∘≥ η′) f

  chrel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A chunk
                                             → W′ ⊩ A chunk
  chrel {⟪ Ψ ⊫ A ⟫} η c = mren (peek≥ η) (syn c) , \ η′ ψ →
                           sem c (η ∘≥ η′) ψ


threls : ∀ {{_ : Model}} {Γ} {W W′ : World} → W′ ≥ W → W ⊩ Γ allthunk
                                            → W′ ⊩ Γ allthunk
threls {∙}     η ∙       = ∙
threls {Γ , A} η (γ , k) = threls η γ , threl {A} η k


chrels : ∀ {{_ : Model}} {Δ} {W W′ : World} → W′ ≥ W → W ⊩ Δ allchunk
                                            → W′ ⊩ Δ allchunk
chrels η δ = maps (chrel η) δ


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


-- TODO: ugh
infix 3 _⊨_valid[_]
_⊨_valid[_] : List Assert → Form → List Form → Set₁
Δ ⊨ A valid[ Γ ] = ∀ {M : Model} {W : World {{M}}} → _⊩_allchunk {{M}} W Δ → _⊩_allthunk {{M}} W Γ
                                                    → _⊩_thunk {{M}} W A


-- TODO: ugh
infix 3 _⊨_allvalid[_]
_⊨_allvalid[_] : List Assert → List Form → List Form → Set₁
Δ ⊨ Ξ allvalid[ Γ ] = ∀ {M : Model} {W : World {{M}}} → _⊩_allchunk {{M}} W Δ → _⊩_allthunk {{M}} W Γ
                                                       → _⊩_allthunk {{M}} W Ξ



thget : ∀ {{_ : Model}} {Γ A} {W : World} → W ⊩ Γ allthunk → Γ ∋ A
                                          → W ⊩ A thunk
thget {Γ = Γ , x} (γ , k) zero    = k
thget {Γ = Γ , x} (γ , l) (suc i) = thget γ i


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
                → Δ ⊨ A valid[ Γ ]
  ↓ (var i)                  {M} δ γ = thget {{M}} γ i
  ↓ (lam {A} {B} 𝒟)          {M} δ γ = return {{M}} {A ⊃ B} (\ η k →
                                         ↓ 𝒟 (chrels {{M}} η δ) (threls {{M}} η γ , k))
  ↓ (app {A} {B} 𝒟 ℰ)        {M} δ γ = bind {{M}} {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                                         f (id≥ {{M}}) (↓ ℰ (chrels {{M}} η δ) (threls {{M}} η γ)))
  ↓ (mvar i ψ)               {M} δ γ = sem {{M}} (get δ i) (id≥ {{M}}) (↓ⁿ ψ δ γ)
  ↓ (box {A} {Ψ} 𝒟)          {M} δ γ = return {{M}} {[ Ψ ] A} (msub (syns {{M}} δ) 𝒟 , \ η′ ψ →
                                         ↓ 𝒟 (chrels {{M}} η′ δ) (threls {{M}} (id≥ {{M}}) ψ))
  ↓ (letbox {A} {B} {Ψ} 𝒟 ℰ) {M} δ γ = bind {{M}} {[ Ψ ] A} {B} (↓ 𝒟 δ γ) (\ η f →
                                         ↓ ℰ (chrels {{M}} η δ , f) (threls {{M}} η γ))

  ↓ⁿ : ∀ {Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                 → Δ ⊨ Ξ allvalid[ Γ ]
  ↓ⁿ ∙       δ γ = ∙
  ↓ⁿ (ξ , 𝒟) δ γ = ↓ⁿ ξ δ γ , ↓ 𝒟 δ γ


--------------------------------------------------------------------------------


ren² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⊢ A neutral[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ′ ]
ren² (η₁ , η₂) 𝒟 = mrenᵣ η₁ (renᵣ η₂ 𝒟)


private
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
              ; peek    = \ { (Δ ⨾ Γ) → Δ }
              ; peek≥   = \ { (η₁ , η₂) → η₁ }
              }


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⊢ A neutral[ Γ ]
                → Δ ⨾ Γ ⊩ A thunk
  ⇓ {ι P}     𝒟 = return {ι P} 𝒟
  ⇓ {A ⊃ B}   𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (ren² η 𝒟) (⇑ k)))
  ⇓ {[ Ψ ] A} 𝒟 = \ η f → letbox (ren² η 𝒟) (f (drop₁ id) (mvz ids , \ η′ ψ →
                    ⇓ (xmvzᵣ (proj₁ η′) (⇑ⁿ ψ))))

  ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊩ A thunk
                → Δ ⊢ A normal[ Γ ]
  ⇑ {ι P}     k = k id (\ η 𝒟 → use 𝒟)
  ⇑ {A ⊃ B}   k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzᵣ))))
  ⇑ {[ Ψ ] A} k = k id (\ η f → box (syn f))

  ⇑ⁿ : ∀ {Ξ Δ Γ} → Δ ⨾ Γ ⊩ Ξ allthunk
                 → Δ ⊢ Ξ allnormal[ Γ ]
  ⇑ⁿ {∙}     ∙       = ∙
  ⇑ⁿ {Ξ , A} (ξ , k) = ⇑ⁿ ξ , ⇑ k


--------------------------------------------------------------------------------


swks : ∀ {A : Form} {Δ : List Assert} {Γ Ξ : List Form} → Δ ⨾ Γ ⊩ Ξ allthunk
                                                        → Δ ⨾ Γ , A ⊩ Ξ allthunk
swks ξ = threls (drop₂ id) ξ


slifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allthunk
                     → Δ ⨾ Γ , A ⊩ Ξ , A allthunk
slifts ξ = swks ξ , ⇓ vzᵣ


svars : ∀ {Δ : List Assert} {Γ Γ′} → Γ′ ⊇ Γ
                                   → Δ ⨾ Γ′ ⊩ Γ allthunk
svars done     = ∙
svars (drop η) = swks (svars η)
svars (keep η) = slifts (svars η)


sids : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Γ allthunk
sids = svars id


--------------------------------------------------------------------------------


smwks : ∀ {A : Assert} {Δ Ξ : List Assert} {Γ : List Form} → Δ ⨾ Γ ⊩ Ξ allchunk
                                                           → Δ , A ⨾ Γ ⊩ Ξ allchunk
smwks ξ = chrels (drop₁ id) ξ


smlifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ allchunk
                      → Δ , A ⨾ Γ ⊩ Ξ , A allchunk
smlifts ξ = smwks ξ , (mvz ids , \ η ψ →
              ⇓ (xmvzᵣ (proj₁ η) (⇑ⁿ ψ)))


smvars : ∀ {Δ Δ′} {Γ : List Form} → Δ′ ⊇ Δ
                                  → Δ′ ⨾ Γ ⊩ Δ allchunk
smvars done     = ∙
smvars (drop η) = smwks (smvars η)
smvars (keep η) = smlifts (smvars η)


smids : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Δ allchunk
smids = smvars id


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⊨ A valid[ Γ ]
              → Δ ⊢ A normal[ Γ ]
↑ f = ⇑ (f smids sids)


nm : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
               → Δ ⊢ A normal[ Γ ]
nm 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
