module BasicIS4.DualContext.Gentzen.KripkeBasicCompleteness where

open import BasicIS4.DualContext.Gentzen.KripkeSoundness public
open import BasicIS4.DualContext.Gentzen.KripkeEquipment public
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
    ; _⊩ᵅ_    = λ { (Γ , Δ) P → Γ ⁏ Δ ⊢ α P }
    ; mono⊩ᵅ  = mono²⊢
    ; ≤⨾R→R   = ≤⨾R→Rᶜ
    ; R⨾≤→R   = R⨾≤→Rᶜ
    ; ≤⊓R→≤⊔R = ≤⊓R→≤⊔Rᶜ
    ; ≤⊔R→≤⊓R = ≤⊔R→≤⊓Rᶜ
    }


-- Soundness and completeness with respect to the canonical model.

--- FIXME: Can we make this true?
postulate
  oops : ∀ {Γ Δ} → (Γ , Δ) Rᶜ (⌀ , Δ)

mutual
  reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , Δ ⊩ A
  reflect {α P}   t = t
  reflect {A ▻ B} t = λ ξ a → reflect {B} (app (mono²⊢ ξ t) (reify {A} a))
  reflect {□ A}   t = λ ζ → reflect {A} (ζ t)
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ Δ} → Γ , Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reify {α P}   s = s
  reify {A ▻ B} s = lam (reify {B} (s weak⊆²ₗ (reflect {A} v₀)))
  reify {□ A}   s = box (reify {A} (s oops))
  reify {A ∧ B} s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}    s = tt

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ , Δ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ Δ} → Γ , Δ ⊩⋆ Π → Γ ⁏ Δ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ Γ ⧺ (□⋆ Δ)
refl⊩⋆ = reflect⋆ refl⊢⋆

refl⊩⋆′ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ Γ
refl⊩⋆′ = reflect⋆ refl⊢⋆′

mrefl⊩⋆′ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆′ = reflect⋆ mrefl⊢⋆′

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Π} → Γ , Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ , Δ′ ⊩⋆ Π → Γ , Δ ⊩⋆ Π
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))

refl⊩⋆″ : ∀ {Δ Δ′ Γ Γ′} → (Γ , Δ) Rᶜ (Γ′ , Δ′) → Γ′ , Δ′ ⊩⋆ Δ
refl⊩⋆″ = reflect⋆ ∘ refl⊢⋆″


-- Completeness, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ᴹ⊩ A → Γ ⁏ Δ ⊢ A
quot t = reify (t refl⊩⋆′ refl⊩⋆″)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ WithRegularForcing.eval
