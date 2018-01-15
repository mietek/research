module SimpleIPLSemantics where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import SimpleIPLDerivations
open import SimpleIPLVerifications


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
            ; Ground = _⊢ᵤ BASE true
            ; _≥_    = _⊇_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renU
            }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ᵤ A true
              → Γ ⊩ A true
  ⇓ {BASE}  𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renU η 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A true
              → Γ ⊢ᵥ A true
  ⇑ {BASE}  𝒟 = use 𝒟
  ⇑ {A ⊃ B} f = lam (⇑ (f (drop id) (⇓ {A} vzU)))


--------------------------------------------------------------------------------


wkS : ∀ {A B Γ} → Γ ⊩ A true
                → Γ , B true ⊩ A true
wkS {A} a = rel {A true} (drop id) a


wksS : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                 → Γ , A true ⊩⋆ Ξ
wksS ξ = rels (drop id) ξ


vzS : ∀ {A Γ} → Γ , A true ⊩ A true
vzS {A} = ⇓ {A} vzU


liftsS : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                   → Γ , A true ⊩⋆ Ξ , A true
liftsS {A} ξ = wksS ξ , vzS {A}


varsS : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩⋆ Γ
varsS done     = ∙
varsS (drop η) = wksS (varsS η)
varsS (keep η) = liftsS (varsS η)


idsS : ∀ {Γ} → Γ ⊩⋆ Γ
idsS = varsS id


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ᵥ A true
↑ f = ⇑ (f idsS)


nbe : ∀ {Γ A} → Γ ⊢ A true
              → Γ ⊢ᵥ A true
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
