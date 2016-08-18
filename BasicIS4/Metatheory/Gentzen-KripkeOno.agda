module BasicIS4.Metatheory.Gentzen-KripkeOno where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.KripkeOno public
open import BasicIS4.Semantics.KripkeCanonicalModelEquipment public

open SyntacticComponent (_⊢_) (mono⊢) (up) (down) (lift) public


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)       γ = (eval t γ refl≤) (eval u γ)
  eval (multibox ts u) γ = λ ζ → eval u (thing ts γ ζ)
  eval (down t)        γ = eval t γ reflR
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  -- TODO: What is this?
  thing : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
  thing {⌀}     ∙        γ ζ = ∙
  thing {Δ , B} (ts , t) γ ζ = thing ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.


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
  reflect {A ▻ B} t = λ η a → reflect (app (mono⊢ η t) (reify a))
  reflect {□ A}   t = λ ζ → reflect (ζ t)
  reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▻ B} s = lam (reify (s weak⊆ (reflect {A} v₀)))
  reify {□ A}   s = let Δ , (ts , ζ) = oops
                    in  multibox ts (reify (s ζ))
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
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

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
