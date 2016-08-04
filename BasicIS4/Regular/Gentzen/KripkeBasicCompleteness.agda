module BasicIS4.Regular.Gentzen.KripkeBasicCompleteness where

open import BasicIS4.Regular.Gentzen.KripkeSoundness public
open import BasicIS4.Regular.Gentzen.KripkeEquipment public
open import BasicIS4.KripkeSemantics public
open RegularForcing public


-- The canonical model.

instance
  canon : Model
  canon = record
    { World    = Worldᶜ
    ; _≤_      = _≤ᶜ_
    ; refl≤    = refl≤ᶜ
    ; trans≤   = trans≤ᶜ
    ; _R_      = _Rᶜ_
    ; reflR    = reflRᶜ
    ; transR   = transRᶜ
    ; _⊩ᵅ_    = λ Γ P → Γ ⊢ α P
    ; mono⊩ᵅ  = mono⊢
    ; ≤⨾R→R   = ≤⨾R→Rᶜ
    ; R⨾≤→R   = R⨾≤→Rᶜ
    ; ≤⊓R→≤⊔R = ≤⊓R→≤⊔Rᶜ
    ; ≤⊔R→≤⊓R = ≤⊔R→≤⊓Rᶜ
    }


-- Soundness and completeness with respect to the canonical model.

--- FIXME: Can we make this true?
postulate
  oops : ∀ {Γ} → ∃ (λ Δ → Γ ⊢⋆ □⋆ Δ × Γ Rᶜ □⋆ Δ)

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = t
  reflect {A ▻ B} t = λ η a → reflect {B} (app (mono⊢ η t) (reify {A} a))
  reflect {□ A}   t = λ ζ → reflect {A} (ζ t)
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▻ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {□ A}   s = let Δ , (ts , ζ) = oops
                    in  multibox ts (reify {A} (s ζ))
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
norm = quot ∘ WithRegularForcing.eval
