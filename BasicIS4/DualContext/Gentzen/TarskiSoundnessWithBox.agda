module BasicIS4.DualContext.Gentzen.TarskiSoundnessWithBox where

open import BasicIS4.TarskiSemantics public
open import BasicIS4.DualContext.Gentzen public


-- Truth for propositions and contexts, inspired by Gabbay and Nanevski.

record Box (A : Ty) : Set where
  constructor [_]
  field
    -- FIXME: Should we not have ⌀ ⁏ ⌀ ⊢ □ A here?
    {Δ} : Cx Ty
    t   : ⌀ ⁏ Δ ⊢ □ A

open ForcingWithBox (Box) public


-- Soundness, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ a → eval t (γ , a) δ
eval (app t u)   γ δ = (eval t γ δ) (eval u γ δ)
eval (mvar i)    γ δ = lookup i δ
-- FIXME: Should evaluation happen here, and not in unbox?
eval (box t)     γ δ = [ box t ] , eval t ∙ δ
eval (unbox t u) γ δ = eval u γ (δ , π₂ (eval t γ δ))
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙
