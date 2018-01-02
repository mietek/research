module StdIPLSemantics where

open import Prelude
open import List
open import StdIPL


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


module _ {{_ : Model}}
  where
    infix 3 _⊩_
    _⊩_ : World → Truth → Set
    W ⊩ BASE true  = Ground W
    W ⊩ A ⊃ B true = ∀ {W′} → W′ ≥ W → W′ ⊩ A true
                             → W′ ⊩ B true

    rel : ∀ {A W W′} → W′ ≥ W → W ⊩ A
                     → W′ ⊩ A
    rel {BASE true}  η 𝒟 = relG η 𝒟
    rel {A ⊃ B true} η f = \ η′ a → f (η ∘≥ η′) a


    infix 3 _⊩⋆_
    _⊩⋆_ : World → List Truth → Set
    W ⊩⋆ Γ = All (W ⊩_) Γ

    rels : ∀ {Γ W W′} → W′ ≥ W → W ⊩⋆ Γ
                      → W′ ⊩⋆ Γ
    rels η γ = mapAll (\ {A} a → rel {A} η a) γ


infix 3 _⊨_
_⊨_ : Context → Truth → Set₁
Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩⋆ Γ
                                  → W ⊩ A true


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ ⊨ A true
↓ (var 𝒾)   γ = lookup γ 𝒾
↓ (lam 𝒟)   γ = \ η a → ↓ 𝒟 (rels η γ , a)
↓ (app 𝒟 ℰ) γ = (↓ 𝒟 γ) id≥ (↓ ℰ γ)


instance
  canon : Model
  canon = record
            { World  = Context
            ; Ground = _⊢ₙₜ BASE true
            ; _≥_    = _⊇_
            ; id≥    = id⊇
            ; _∘≥_   = _∘⊇_
            ; relG   = renₙₜ
            }

mutual
  ⇓ : ∀ {A Γ} → Γ ⊢ₙₜ A true
              → Γ ⊩ A true
  ⇓ {BASE}  𝒟 = 𝒟
  ⇓ {A ⊃ B} 𝒟 = \ η a → ⇓ (app (renₙₜ η 𝒟) (⇑ a))

  ⇑ : ∀ {A Γ} → Γ ⊩ A true
              → Γ ⊢ₙₘ A true
  ⇑ {BASE}  𝒟 = nt 𝒟
  ⇑ {A ⊃ B} f = lam (⇑ (f (drop id⊇) (⇓ {A} vzₙₜ)))


swk : ∀ {A B Γ} → Γ ⊩ A
                → Γ , B true ⊩ A
swk {A} a = rel {A} (drop id⊇) a

svz : ∀ {A Γ} → Γ , A true ⊩ A true
svz {A} = ⇓ {A} vzₙₜ


swks : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                 → Γ , A true ⊩⋆ Ξ
swks ξ = rels (drop id⊇) ξ

slifts : ∀ {A Γ Ξ} → Γ ⊩⋆ Ξ
                   → Γ , A true ⊩⋆ Ξ , A true
slifts {A} ξ = swks ξ , svz {A}

sids : ∀ {Γ} → Γ ⊩⋆ Γ
sids {∙}          = ∙
sids {Γ , A true} = slifts sids


↑ : ∀ {Γ A} → Γ ⊨ A true
            → Γ ⊢ₙₘ A true
↑ f = ⇑ (f sids)


nbe : ∀ {Γ A} → Γ ⊢ A true
              → Γ ⊢ₙₘ A true
nbe 𝒟 = ↑ (↓ 𝒟)
