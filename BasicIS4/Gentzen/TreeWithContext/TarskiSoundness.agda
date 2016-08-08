module BasicIS4.Gentzen.TreeWithContext.TarskiSoundness where

open import BasicIS4.Gentzen.TreeWithContext public
open import BasicIS4.TarskiSemantics public




-- Using truth with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⊢_) public


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: How to write this without translation?
  postulate
    oops : ∀ {A Δ} → □⋆ Δ ⊢ A → ⌀ ⊢ A

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ a → eval t (γ , a)
    eval (app t u)       γ = (eval t γ) (eval u γ)
    eval (multibox ts u) γ = oops u , eval u (eval⋆ ts γ)
    eval (down t)        γ = let s , a = eval t γ
                             in a
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊨⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
