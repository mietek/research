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

      Ground : World → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {W W′} → W′ ≥ W → Ground W
                      → Ground W′

      ⌊_⌋ : World → List² Validity Truth

      ⌊_⌋≥ : ∀ {W W′} → W′ ≥ W
                      → ⌊ W′ ⌋ ⊇² ⌊ W ⌋

open Model {{...}}


--------------------------------------------------------------------------------


⌊_⌋₁ : ∀ {{_ : Model}} → World → List Validity
⌊ W ⌋₁ = proj₁ ⌊ W ⌋


⌊_⌋₂ : ∀ {{_ : Model}} → World → List Truth
⌊ W ⌋₂ = proj₂ ⌊ W ⌋


⌊_⌋≥₁ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₁ ⊇ ⌊ W ⌋₁
⌊ η ⌋≥₁ = proj₁ ⌊ η ⌋≥


⌊_⌋≥₂ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₂ ⊇ ⌊ W ⌋₂
⌊ η ⌋≥₂ = proj₂ ⌊ η ⌋≥


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊩ BASE true  = Ground W
  W ⊩ A ⊃ B true = ∀ {W′} → W′ ≥ W → W′ ⊪ A true
                           → W′ ⊪ B true
  W ⊩ □ A true   = W ⊪₁ A valid

  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊪ A true = ∀ {B W′} → W′ ≥ W → (∀ {W″} → W″ ≥ W′ → W″ ⊩ A true
                                              → ⌊ W″ ⌋₁ ⨾ ⌊ W″ ⌋₂ ⊢ₗ B)
                         → ⌊ W′ ⌋₁ ⨾ ⌊ W′ ⌋₂ ⊢ₗ B

  infix 3 _⊪₁_
  _⊪₁_ : ∀ {{_ : Model}} → World → Validity → Set
  W ⊪₁ A valid = ⌊ W ⌋₁ ⊢₁ A valid × W ⊪ A true


infix 3 _⊪⋆_
_⊪⋆_ : ∀ {{_ : Model}} → World → List Truth → Set
W ⊪⋆ Γ = All (W ⊪_) Γ


infix 3 _⊪⋆₁_
_⊪⋆₁_ : ∀ {{_ : Model}} → World → List Validity → Set
W ⊪⋆₁ Δ = All (W ⊪₁_) Δ


--------------------------------------------------------------------------------


syn : ∀ {{_ : Model}} {A W} → W ⊪₁ A valid
                            → ⌊ W ⌋₁ ⊢₁ A valid
syn v = proj₁ v


syns : ∀ {{_ : Model}} {Δ W} → W ⊪⋆₁ Δ
                             → ⌊ W ⌋₁ ⊢⋆₁ Δ
syns δ = maps syn δ


sem : ∀ {{_ : Model}} {A W} → W ⊪₁ A valid
                            → W ⊪ A true
sem v = proj₂ v


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A
                                 → W′ ⊩ A
  rel {BASE true}  η 𝒟 = relG η 𝒟
  rel {A ⊃ B true} η f = \ η′ k → f (η ∘≥ η′) k
  rel {□ A true}   η v = relC₁ η v

  relC : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊪ A
                                  → W′ ⊪ A
  relC η k = \ η′ f → k (η ∘≥ η′) f

  relC₁ : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊪₁ A
                                   → W′ ⊪₁ A
  relC₁ {A valid} η v = mren ⌊ η ⌋≥₁ (syn v) ,
                        relC {A true} η (sem v)


relsC : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊪⋆ Γ
                                 → W′ ⊪⋆ Γ
relsC η γ = maps (\ {A} k {B} {W′} → relC {A} η (\ {C} {W″} → k {C} {W″})) γ
-- NOTE: Pattern-matching problem here prevents rel from taking “A true”
-- NOTE: Equivalent to
-- relsC η γ = maps (relC η) γ


relsC₁ : ∀ {{_ : Model}} {Δ W W′} → W′ ≥ W → W ⊪⋆₁ Δ
                                  → W′ ⊪⋆₁ Δ
relsC₁ η δ = maps (relC₁ η) δ


--------------------------------------------------------------------------------


return : ∀ {{_ : Model}} {A W} → W ⊩ A true
                               → W ⊪ A true
return {A} a = \ η f → f id≥ (rel {A true} η a)


bind : ∀ {{_ : Model}} {A B W} → W ⊪ A true → (∀ {W′} → W′ ≥ W → W′ ⊩ A true
                                                         → W′ ⊪ B true)
                               → W ⊪ B true
bind k f = \ η f′ →
             k η (\ η′ a →
               f (η ∘≥ η′) a id≥ (\ η″ b →
                 f′ (η′ ∘≥ η″) b))


--------------------------------------------------------------------------------


infix 3 _⊨_
_⊨_ : List² Validity Truth → Truth → Set₁
Δ ⨾ Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊪⋆₁ Δ → W ⊪⋆ Γ
                                      → W ⊪ A true


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊨ A true
↓ (var i)              δ γ = get γ i
↓ (lam {A} {B} 𝒟)      δ γ = return {A ⊃ B} (\ η k →
                               ↓ 𝒟 (relsC₁ η δ) (relsC η γ , k))
↓ (app {A} {B} 𝒟 ℰ)    δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                               f id≥ (↓ ℰ (relsC₁ η δ) (relsC η γ)))
↓ (mvar i)             δ γ = sem (get δ i)
↓ (box {A} 𝒟)          δ γ = return {□ A} (msub (syns δ) 𝒟 , ↓ 𝒟 δ ∙)
↓ (letbox {A} {B} 𝒟 ℰ) δ γ = bind {□ A} {B} (↓ 𝒟 δ γ) (\ η v →
                               ↓ ℰ (relsC₁ η δ , v) (relsC η γ))


--------------------------------------------------------------------------------


renR² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ᵣ A true
                        → Δ′ ⨾ Γ′ ⊢ᵣ A true
renR² η 𝒟 = mrenR (proj₁ η) (renR (proj₂ η) 𝒟)


instance
  canon : Model
  canon = record
            { World  = List² Validity Truth
            ; Ground = \ { (Δ ⨾ Γ) → Δ ⨾ Γ ⊢ᵣ BASE true }
            ; _≥_    = _⊇²_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renR²
            ; ⌊_⌋    = id
            ; ⌊_⌋≥   = id
            }


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ᵣ A true
                → Δ ⨾ Γ ⊪ A true
  ⇓ {BASE}  𝒟 = return {BASE} 𝒟
  ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renR² η 𝒟) (⇑ k)))
  ⇓ {□ A}   𝒟 = \ η f → letbox (renR² η 𝒟) (f (drop₁ id) (mvz , ⇓ mvzR))

  ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊪ A true
                → Δ ⨾ Γ ⊢ₗ A true
  ⇑ {BASE}  k = k id (\ η 𝒟 → use 𝒟)
  ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzR))))
  ⇑ {□ A}   k = k id (\ η v → box (syn v))


--------------------------------------------------------------------------------


wksS : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆ Ξ
                   → Δ ⨾ Γ , A true ⊪⋆ Ξ
wksS ξ = relsC (drop₂ id) ξ


liftsS : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆ Ξ
                     → Δ ⨾ Γ , A true ⊪⋆ Ξ , A true
liftsS ξ = wksS ξ , ⇓ vzR


varsS : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                   → Δ ⨾ Γ′ ⊪⋆ Γ
varsS done     = ∙
varsS (drop η) = wksS (varsS η)
varsS (keep η) = liftsS (varsS η)


idsS : ∀ {Δ Γ} → Δ ⨾ Γ ⊪⋆ Γ
idsS = varsS id


--------------------------------------------------------------------------------


mwksS₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆₁ Ξ
                     → Δ , A valid ⨾ Γ ⊪⋆₁ Ξ
mwksS₁ ξ = relsC₁ (drop₁ id) ξ


mliftsS₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆₁ Ξ
                       → Δ , A valid ⨾ Γ ⊪⋆₁ Ξ , A valid
mliftsS₁ ξ = mwksS₁ ξ , (mvz , ⇓ mvzR)


mvarsS₁ : ∀ {Δ Δ′ Γ} → Δ′ ⊇ Δ
                     → Δ′ ⨾ Γ ⊪⋆₁ Δ
mvarsS₁ done     = ∙
mvarsS₁ (drop η) = mwksS₁ (mvarsS₁ η)
mvarsS₁ (keep η) = mliftsS₁ (mvarsS₁ η)


midsS₁ : ∀ {Δ Γ} → Δ ⨾ Γ ⊪⋆₁ Δ
midsS₁ = mvarsS₁ id


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊨ A true
              → Δ ⨾ Γ ⊢ₗ A true
↑ f = ⇑ (f midsS₁ idsS)


nbe : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ Γ ⊢ₗ A true
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
