{-# OPTIONS --rewriting #-}

module A201801.IPLStandardNormalisation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.IPLPropositions
open import A201801.IPLStandardDerivations
open import A201801.IPLStandardBidirectionalDerivations-NormalNeutral


--------------------------------------------------------------------------------


record Model : Set₁
  where
    field
      World : Set

      -- TODO: Better name
      Ground : World → String → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {P W W′} → W′ ≥ W → Ground W P
                        → Ground W′ P

open Model {{...}} public


--------------------------------------------------------------------------------


infix 3 _⊩_value
_⊩_value : ∀ {{_ : Model}} → World → Form → Set
W ⊩ ι P value   = Ground W P
W ⊩ A ⊃ B value = ∀ {W′ : World} → W′ ≥ W → W′ ⊩ A value
                                  → W′ ⊩ B value


infix 3 _⊩_allvalue
_⊩_allvalue : ∀ {{_ : Model}} → World → List Form → Set
W ⊩ Γ allvalue = All (W ⊩_value) Γ


--------------------------------------------------------------------------------


rel : ∀ {{_ : Model}} {A} {W W′ : World} → W′ ≥ W → W ⊩ A value
                                         → W′ ⊩ A value
rel {ι P}   η 𝒟 = relG η 𝒟
rel {A ⊃ B} η f = \ η′ a → f (η ∘≥ η′) a


rels : ∀ {{_ : Model}} {Γ} {W W′ : World} → W′ ≥ W → W ⊩ Γ allvalue
                                          → W′ ⊩ Γ allvalue
rels η γ = maps (\ { {A} a → rel {A} η a }) γ


--------------------------------------------------------------------------------


-- TODO: ugh
infix 3 _⊨_true
_⊨_true : List Form → Form → Set₁
Γ ⊨ A true = ∀ {M : Model} {W : World {{M}}} → _⊩_allvalue {{M}} W Γ
                                              → _⊩_value {{M}} W A


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var i)       γ = get γ i
↓ (lam 𝒟)   {M} γ = \ η a → ↓ 𝒟 (rels {{M}} η γ , a)
↓ (app 𝒟 ℰ) {M} γ = (↓ 𝒟 γ) (id≥ {{M}}) (↓ ℰ γ)


--------------------------------------------------------------------------------


private
  instance
    canon : Model
    canon = record
              { World  = List Form
              ; Ground = \ Γ P → Γ ⊢ ι P neutral
              ; _≥_    = _⊇_
              ; id≥    = id
              ; _∘≥_   = _∘_
              ; relG   = renᵣ
              }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ A neutral
              → Γ ⊩ A value
  ⇓ {ι P}   𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renᵣ η 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A value
              → Γ ⊢ A normal
  ⇑ {ι P}   𝒟 = neu 𝒟
  ⇑ {A ⊃ B} f = lam (⇑ (f (drop id) (⇓ {A} vzᵣ)))


--------------------------------------------------------------------------------


swks : ∀ {A : Form} {Γ Ξ : List Form} → Γ ⊩ Ξ allvalue
                                      → Γ , A ⊩ Ξ allvalue
swks ξ = rels (drop id) ξ


slifts : ∀ {A Γ Ξ} → Γ ⊩ Ξ allvalue
                   → Γ , A ⊩ Ξ , A allvalue
slifts {A} ξ = swks ξ , ⇓ {A} vzᵣ


svars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩ Γ allvalue
svars done     = ∙
svars (drop η) = swks (svars η)
svars (keep η) = slifts (svars η)


sids : ∀ {Γ} → Γ ⊩ Γ allvalue
sids = svars id


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ A normal
↑ f = ⇑ (f sids)


nm : ∀ {Γ A} → Γ ⊢ A true
             → Γ ⊢ A normal
nm 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
