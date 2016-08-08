module BasicIS4.Hilbert.TreeWithContextPair.TarskiSoundness where

open import BasicIS4.Hilbert.TreeWithContextPair public
open import BasicIS4.TarskiSemantics public




-- Using truth with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⁏ ⌀ ⊢_) public


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: This formalisation seems to prohibit closed syntax.
  postulate
    oops : ∀ {A Δ} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ⌀ ⊢ A

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)   γ δ = lookup i γ
  eval (app t u) γ δ = (eval t γ δ) (eval u γ δ)
  eval ci        γ δ = id
  eval ck        γ δ = const
  eval cs        γ δ = ap
  eval (mvar i)  γ δ = lookup i δ
  eval (box t)   γ δ = oops t , eval t ∙ δ
  eval cdist     γ δ = λ { (t , f) (u , a) → app t u , f a }
  eval cup       γ δ = λ { (t , a) → box t , (t , a) }
  eval cdown     γ δ = λ { (t , a) → a }
  eval cpair     γ δ = _,_
  eval cfst      γ δ = π₁
  eval csnd      γ δ = π₂
  eval tt        γ δ = ∙
