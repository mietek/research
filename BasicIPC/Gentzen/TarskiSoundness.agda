module BasicIPC.Gentzen.TarskiSoundness where

open import BasicIPC.Gentzen public
open import BasicIPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)    γ = lookup i γ
  eval (lam t)    γ = λ a → eval t (γ , a)
  eval (app t u)  γ = (eval t γ) (eval u γ)
  eval (pair t u) γ = eval t γ , eval u γ
  eval (fst t)    γ = π₁ (eval t γ)
  eval (snd t)    γ = π₂ (eval t γ)
  eval tt         γ = ∙
