module BasicIS4.Metatheory.Gentzen-TarskiGabbayNanevski where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiGabbayNanevski public


open SyntacticComponent (_⊢_) (_⊢⋆_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ in t
  reify {□ A}   s       = let t , f = s refl⊆ in box t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Π Γ} → Γ ⊨⋆ Π → Γ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

-- FIXME: Ugh?
postulate
  multioops : ∀ {A Γ Δ} → Γ ⊢⋆ □⋆ Δ → □⋆ Δ ⊢ A → ⌀ ⊢ A

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ η → multicut (reify⋆ (mono⊨⋆ η γ)) (lam t) , λ a →
                             eval t (mono⊨⋆ η γ , a)
  eval (app t u)       γ = eval t γ ⟪$⟫ eval u γ
  eval (multibox ts u) γ = λ η → multioops ts u , eval u (eval⋆ ts (mono⊨⋆ η γ))
  eval (down t)        γ = ⟪⇓⟫ (eval t γ)
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → ∀ᴹ⊨ Γ ⇒⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊨ᵅ_   = λ Γ P → Γ ⊢ α P
    ; mono⊨ᵅ = mono⊢
    }


-- Soundness with respect to the canonical model.

-- FIXME: The semantics must be wrong...
postulate
  oops : ∀ {A Γ} → Γ ⊢ A → ⌀ ⊢ A

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η → mono⊢ η t , λ a → reflect (app (mono⊢ η t) (reify a))
reflect {□ A}   t = λ η → oops (down (mono⊢ η t)) , reflect (down (mono⊢ η t))
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

refl⊨⋆ : ∀ {Γ} → Γ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆

trans⊨⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊨⋆ Γ′ → Γ′ ⊨⋆ Γ″ → Γ ⊨⋆ Γ″
trans⊨⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → ∀ᴹ⊨ Γ ⇒ A → Γ ⊢ A
quot t = reify (t refl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
