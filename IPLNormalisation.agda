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
      Ground : World → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {W W′} → W′ ≥ W → Ground W
                      → Ground W′

open Model {{...}}


--------------------------------------------------------------------------------


infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Truth → Set
W ⊩ BASE true  = Ground W
W ⊩ A ⊃ B true = ∀ {W′} → W′ ≥ W → W′ ⊩ A true
                         → W′ ⊩ B true


infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{_ : Model}} → World → List Truth → Set
W ⊩⋆ Γ = All (W ⊩_) Γ


--------------------------------------------------------------------------------


rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A
                               → W′ ⊩ A
rel {BASE true}  η 𝒟 = relG η 𝒟
rel {A ⊃ B true} η f = \ η′ a → f (η ∘≥ η′) a


rels : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊩⋆ Γ
                                → W′ ⊩⋆ Γ
rels η γ = maps (\ { {A} a → rel {A} η a }) γ


--------------------------------------------------------------------------------


infix 3 _⊨_
_⊨_ : List Truth → Truth → Set₁
Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩⋆ Γ
                                  → W ⊩ A true


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var i)   γ = get γ i
↓ (lam 𝒟)   γ = \ η a → ↓ 𝒟 (rels η γ , a)
↓ (app 𝒟 ℰ) γ = (↓ 𝒟 γ) id≥ (↓ ℰ γ)


--------------------------------------------------------------------------------


instance
  canon : Model
  canon = record
            { World  = List Truth
            ; Ground = _⊢ᵣ BASE true
            ; _≥_    = _⊇_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renᵣ
            }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ᵣ A true
              → Γ ⊩ A true
  ⇓ {BASE}  𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renᵣ η 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A true
              → Γ ⊢ₗ A true
  ⇑ {BASE}  𝒟 = use 𝒟
  ⇑ {A ⊃ B} f = lam (⇑ (f (drop id) (⇓ {A} vzᵣ)))


--------------------------------------------------------------------------------


wkₛ : ∀ {A B Γ} → Γ ⊩ A true
                → Γ , B true ⊩ A true
wkₛ {A} a = rel {A true} (drop id) a


wksₛ : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                 → Γ , A true ⊩⋆ Ξ
wksₛ ξ = rels (drop id) ξ


vzₛ : ∀ {A Γ} → Γ , A true ⊩ A true
vzₛ {A} = ⇓ {A} vzᵣ


liftsₛ : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                   → Γ , A true ⊩⋆ Ξ , A true
liftsₛ {A} ξ = wksₛ ξ , vzₛ {A}


varsₛ : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩⋆ Γ
varsₛ done     = ∙
varsₛ (drop η) = wksₛ (varsₛ η)
varsₛ (keep η) = liftsₛ (varsₛ η)


idsₛ : ∀ {Γ} → Γ ⊩⋆ Γ
idsₛ = varsₛ id


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ₗ A true
↑ f = ⇑ (f idsₛ)


nbe : ∀ {Γ A} → Γ ⊢ A true
              → Γ ⊢ₗ A true
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
