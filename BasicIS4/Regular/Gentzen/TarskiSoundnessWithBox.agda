module BasicIS4.Regular.Gentzen.TarskiSoundnessWithBox where

open import BasicIS4.TarskiSemantics public
open import BasicIS4.Regular.Gentzen public


-- Truth for propositions and contexts, inspired by Gabbay and Nanevski.

record Box (A : Ty) : Set where
  constructor [_]
  field
    -- FIXME: Should we not have ⌀ ⊢ □ A here?
    {Δ} : Cx Ty
    t   : □⋆ Δ ⊢ □ A

open ForcingWithBox (Box) public


-- Soundness, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ a → eval t (γ , a)
  eval (app t u)       γ = (eval t γ) (eval u γ)
  -- FIXME: Should evaluation happen here, and not in down?
  eval (multibox ts u) γ = [ lift u ] , eval u (eval⋆ ts γ)
  eval (down t)        γ = π₂ (eval t γ)
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {Δ Γ} → Γ ⊢⋆ Δ → Γ ᴹ⊨⋆ Δ
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Δ , A} (ts , t) γ = eval⋆ ts γ , eval t γ
