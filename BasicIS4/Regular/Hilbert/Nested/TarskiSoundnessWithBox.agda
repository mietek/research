module BasicIS4.Regular.Hilbert.Nested.TarskiSoundnessWithBox where

open import BasicIS4.TarskiSemantics public
open import BasicIS4.Regular.Hilbert.Nested public


-- Truth for propositions and contexts, inspired by Gabbay and Nanevski.

record Box (A : Ty) : Set where
  constructor [_]
  field
    t : ⌀ ⊢ □ A

open ForcingWithBox (Box) public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = (eval t γ) (eval u γ)
eval ci        γ = id
eval ck        γ = const
eval cs        γ = ap
-- FIXME: Should evaluation happen here, and not in cdown?
eval (box t)   γ = [ lift t ] , eval t ∙
eval cdist     γ = λ { ([ t ] , □f) ([ u ] , □a) → [ dist t u ] , □f □a }
eval cup       γ = λ { ([ t ] , □a) → [ up t ] , ([ t ] , □a) }
eval cdown     γ = λ { ([ t ] , □a) → □a }
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval tt        γ = ∙
