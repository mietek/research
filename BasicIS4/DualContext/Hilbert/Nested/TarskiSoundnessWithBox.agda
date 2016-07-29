module BasicIS4.DualContext.Hilbert.Nested.TarskiSoundnessWithBox where

open import BasicIS4.TarskiSemantics public
open import BasicIS4.DualContext.Hilbert.Nested public


-- Truth for propositions and contexts, inspired by Gabbay and Nanevski.

record Box (A : Ty) : Set where
  constructor [_]
  field
    -- FIXME: Should we not have ⌀ ⁏ ⌀ ⊢ □ A here?
    {Δ} : Cx Ty
    t   : ⌀ ⁏ Δ ⊢ □ A

open ForcingWithBox (Box) public


-- FIXME: This formalisation exposes the problem that the modal contexts
-- of open syntax fragments are not connected to each other.
postulate
  oops : ∀ {A Δ ∇} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ∇ ⊢ A


-- Soundness, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = (eval t γ δ) (eval u γ δ)
eval ci        γ δ = id
eval ck        γ δ = const
eval cs        γ δ = ap
eval (mvar i)  γ δ = lookup i δ
-- FIXME: Should evaluation happen here, and not in cdown?
eval (box t)   γ δ = [ lift t ] , eval t ∙ δ
eval cdist     γ δ = λ { ([ t ] , □f) ([ u ] , □a) → [ dist t (oops u) ] , □f □a }
eval cup       γ δ = λ { ([ t ] , □a) → [ up t ] , ([ t ] , □a) }
eval cdown     γ δ = λ { ([ t ] , □a) → □a }
eval cpair     γ δ = _,_
eval cfst      γ δ = π₁
eval csnd      γ δ = π₂
eval tt        γ δ = ∙
