module BasicIS4.Gentzen.TreeWithContextPair.TarskiSoundness where

open import BasicIS4.Gentzen.TreeWithContextPair public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⁏ ⌀ ⊢_) public


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: How to write this without translation?
  postulate
    oops : ∀ {A Δ} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ⌀ ⊢ A

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ a → eval t (γ , a) δ
  eval (app t u)   γ δ = (eval t γ δ) (eval u γ δ)
  eval (mvar i)    γ δ = lookup i δ
  eval (box t)     γ δ = oops t , eval t ∙ δ
  eval (unbox t u) γ δ = let s , a = eval t γ δ
                         in  eval u γ (δ , a)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙
