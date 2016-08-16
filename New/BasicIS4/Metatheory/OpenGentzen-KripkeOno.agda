module New.BasicIS4.Metatheory.OpenGentzen-KripkeOno where

open import New.BasicIS4.Syntax.OpenGentzen public
open import New.BasicIS4.Semantics.KripkeOno public
open import New.BasicIS4.Semantics.KripkeCanonicalModelEquipment public

open SyntacticComponent (_⊢_) (mono⊢) (up) (down) (lift) public


mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)       γ = (eval t γ refl≤) (eval u γ)
  eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
  eval (down t)        γ = eval t γ reflR
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
  eval⋆ {⌀}     ∙        γ ζ = ∙
  eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)


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
norm = quot ∘ eval
