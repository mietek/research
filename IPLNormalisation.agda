module IPLNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import IPLDerivations
open import IPLBidirectionalDerivationsForNormalisation


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

open Model {{...}}


--------------------------------------------------------------------------------


infix 3 _⊩_value
_⊩_value : ∀ {{_ : Model}} → World → Prop → Set
W ⊩ ι P value   = Ground W P
W ⊩ A ⊃ B value = ∀ {W′} → W′ ≥ W → W′ ⊩ A value
                          → W′ ⊩ B value


infix 3 _⊩_allvalue
_⊩_allvalue : ∀ {{_ : Model}} → World → List Prop → Set
W ⊩ Γ allvalue = All (W ⊩_value) Γ


--------------------------------------------------------------------------------


rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A value
                               → W′ ⊩ A value
rel {ι P}   η 𝒟 = relG η 𝒟
rel {A ⊃ B} η f = \ η′ a → f (η ∘≥ η′) a


rels : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊩ Γ allvalue
                                → W′ ⊩ Γ allvalue
rels η γ = maps (\ { {A} a → rel {A} η a }) γ


--------------------------------------------------------------------------------


infix 3 _⊨_true
_⊨_true : List Prop → Prop → Set₁
Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩ Γ allvalue
                                  → W ⊩ A value


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var i)   γ = get γ i
↓ (lam 𝒟)   γ = \ η a → ↓ 𝒟 (rels η γ , a)
↓ (app 𝒟 ℰ) γ = (↓ 𝒟 γ) id≥ (↓ ℰ γ)


--------------------------------------------------------------------------------


instance
  canon : Model
  canon = record
            { World  = List Prop
            ; Ground = \ Γ P → Γ ⊢ ι P usable
            ; _≥_    = _⊇_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renᵣ
            }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ A usable
              → Γ ⊩ A value
  ⇓ {ι P}   𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renᵣ η 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A value
              → Γ ⊢ A verifiable
  ⇑ {ι P}   𝒟 = use 𝒟
  ⇑ {A ⊃ B} f = lam (⇑ (f (drop id) (⇓ {A} vzᵣ)))


--------------------------------------------------------------------------------


wkₛ : ∀ {A B Γ} → Γ ⊩ A value
                → Γ , B ⊩ A value
wkₛ {A} a = rel {A} (drop id) a


wksₛ : ∀ {A Γ Ξ} → Γ ⊩ Ξ allvalue
                 → Γ , A ⊩ Ξ allvalue
wksₛ ξ = rels (drop id) ξ


vzₛ : ∀ {A Γ} → Γ , A ⊩ A value
vzₛ {A} = ⇓ {A} vzᵣ


liftsₛ : ∀ {A Γ Ξ} → Γ ⊩ Ξ allvalue
                   → Γ , A ⊩ Ξ , A allvalue
liftsₛ {A} ξ = wksₛ ξ , vzₛ {A}


varsₛ : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩ Γ allvalue
varsₛ done     = ∙
varsₛ (drop η) = wksₛ (varsₛ η)
varsₛ (keep η) = liftsₛ (varsₛ η)


idsₛ : ∀ {Γ} → Γ ⊩ Γ allvalue
idsₛ = varsₛ id


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ A verifiable
↑ f = ⇑ (f idsₛ)


nm : ∀ {Γ A} → Γ ⊢ A true
             → Γ ⊢ A verifiable
nm 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
