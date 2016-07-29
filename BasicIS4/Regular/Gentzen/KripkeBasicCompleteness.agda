module BasicIS4.Regular.Gentzen.KripkeBasicCompleteness where

open import BasicIS4.Regular.Gentzen.KripkeSoundness public
open import BasicIS4.Regular.Gentzen.KripkeEquipment public
open import BasicIS4.KripkeSemantics.Ono public
open StandardForcing public


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Worldᶜ
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _R_     = _Rᶜ_
    ; reflR   = reflRᶜ
    ; transR  = transRᶜ
    ; _⊩ᵅ_   = λ w P → w ⊢ α P
    ; mono⊩ᵅ = mono⊢
    ; zigR    = zigRᶜ
    }


-- Soundness and completeness with respect to the canonical model.

--- FIXME: This is almost certainly false.
postulate
  oops : ∀ {Γ} → Γ ⊢⋆ □⋆ Γ

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ η a → reflect {B} (app (mono⊢ η t) (reify {A} a))
  reflect {□ A}   t = λ ζ → reflect {A} (ζ t)
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▷ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {□ A}   s = multibox oops (reify {A} (s liftRᶜ))
  reify {A ∧ B} s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}    s = tt

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ Ono.eval
