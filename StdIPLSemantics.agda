{-# OPTIONS --rewriting #-}

module StdIPLSemantics where

open import Prelude
open import List
open import AllList
open import StdIPLPropositions
open import StdIPLDerivations
open import StdIPLVerifications


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


rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A
                               → W′ ⊩ A
rel {BASE true}  η 𝒟 = relG η 𝒟
rel {A ⊃ B true} η f = \ η′ a → f (η ∘≥ η′) a


--------------------------------------------------------------------------------


infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{_ : Model}} → World → List Truth → Set
W ⊩⋆ Γ = All (W ⊩_) Γ


rels : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊩⋆ Γ
                                → W′ ⊩⋆ Γ
rels η γ = maps (\ {A} a → rel {A} η a) γ


--------------------------------------------------------------------------------


infix 3 _⊨_
_⊨_ : List Truth → Truth → Set₁
Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩⋆ Γ
                                  → W ⊩ A true


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var 𝒾)   γ = get γ 𝒾
↓ (lam 𝒟)   γ = \ η a → ↓ 𝒟 (rels η γ , a)
↓ (app 𝒟 ℰ) γ = (↓ 𝒟 γ) id≥ (↓ ℰ γ)


--------------------------------------------------------------------------------


postulate
  id-t2u-u2t : ∀ {Γ} → map t→u (map u→t Γ) ≡ Γ
  id-u2t-t2u : ∀ {Γ} → map u→t (map t→u Γ) ≡ Γ

{-# REWRITE id-t2u-u2t #-}
{-# REWRITE id-u2t-t2u #-}



instance
  canon : Model
  canon = record
            { World  = List Truth
            ; Ground = \ Γ → map t→u Γ ⊢ᵣ BASE usable
            ; _≥_    = _⊇_
            ; id≥    = id⊇
            ; _∘≥_   = _∘⊇_
            ; relG   = \ η 𝒟 → renᵣ (map⊇ η) 𝒟
            }


mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ᵣ A usable
              → map u→t Γ ⊩ A true
  ⇓ {BASE}  𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renᵣ (map⊇ η) 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A true
              → map t→u Γ ⊢ₙ A verified
  ⇑ {BASE}      𝒟 = use 𝒟
  ⇑ {A ⊃ B} {Γ} f = lam (⇑ (f (drop id⊇) (⇓ {A} {map t→u Γ , A usable} vzᵣ)))


--------------------------------------------------------------------------------


swk : ∀ {A B Γ} → Γ ⊩ A
                → Γ , B true ⊩ A
swk {A} a = rel {A} (drop id⊇) a


svz : ∀ {A Γ} → Γ , A true ⊩ A true
svz {A} {Γ} = ⇓ {A} {map t→u Γ , A usable} vzᵣ


--------------------------------------------------------------------------------


swks : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                 → Γ , A true ⊩⋆ Ξ
swks ξ = rels (drop id⊇) ξ


slifts : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                   → Γ , A true ⊩⋆ Ξ , A true
slifts {A} ξ = swks ξ , svz {A}


svars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                 → Γ′ ⊩⋆ Γ
svars done     = ∙
svars (drop η) = swks (svars η)
svars (keep η) = slifts (svars η)


sids : ∀ {Γ} → Γ ⊩⋆ Γ
sids = svars id⊇


--------------------------------------------------------------------------------


↑ : ∀ {Γ A} → Γ ⊨ A true
            → map t→u Γ ⊢ₙ A verified
↑ f = ⇑ (f sids)


nbe : ∀ {Γ A} → Γ ⊢ A true
              → map t→u Γ ⊢ₙ A verified
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
