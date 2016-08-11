module BasicIS4.Hilbert.TreeWithContext.TarskiSoundness where

open import BasicIS4.Hilbert.TreeWithContext public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⊢_) (app) (box) public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval (box t)   γ = t , eval t ∙
  eval cdist     γ = distˢ
  eval cup       γ = upˢ
  eval cdown     γ = downˢ
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙
