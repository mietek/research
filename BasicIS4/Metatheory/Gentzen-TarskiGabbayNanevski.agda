module BasicIS4.Metatheory.Gentzen-TarskiGabbayNanevski where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiGabbayNanevski public

open SyntacticComponent (⌀ ⊢_) (app) (box) public


-- Completeness with respect to a particular model.

-- FIXME: This formalisation seems to require a Coquand-Dybjer semantics.
postulate
  oopsα : ∀ {P} → ⌀ ⊢ α P
  oops▻ : ∀ {A B} → ⌀ ⊢ A ▻ B

reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⊢ A
reify {α P}   s       = oopsα
reify {A ▻ B} s       = oops▻
reify {□ A}   (t , s) = box t
reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
reify {⊤}    ∙       = tt

reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ a → eval t (γ , a)
  eval (app t u)       γ = (eval t γ) (eval u γ)
  eval (multibox ts u) γ = multicut (reify⋆ γ) (down (multibox ts u)) ,
                           eval u (eval⋆ ts γ)
  eval (down t)        γ = downˢ (eval t γ)
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊨⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
