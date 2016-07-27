module IPC.Gentzen.TarskiSoundness where

open import IPC.TarskiSemantics public
open import IPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)      γ = lookup i γ
eval (lam t)      γ = λ a → eval t (γ , a)
eval (app t u)    γ = (eval t γ) (eval u γ)
eval (pair t u)   γ = eval t γ , eval u γ
eval (fst t)      γ = π₁ (eval t γ)
eval (snd t)      γ = π₂ (eval t γ)
eval tt           γ = ∙
eval (boom t)     γ = elimBot (eval t γ)
eval (inl t)      γ = ι₁ (eval t γ)
eval (inr t)      γ = ι₂ (eval t γ)
eval (case t u v) γ = κ (eval t γ)
                        (λ a → eval u (γ , a))
                        (λ b → eval v (γ , b))
