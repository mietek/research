module BasicIPC.Gentzen.KripkeSoundness.Godel where

open import BasicIPC.KripkeSemantics.Godel public
open import BasicIPC.Gentzen public


-- Soundness, or evaluation, based on the Gödel translation of IPC to S4.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
eval (pair t u) γ = λ ξ → let γ′ = mono⊩⋆ ξ γ
                           in  eval t γ′ , eval u γ′
eval (fst t)    γ = π₁ (eval t γ refl≤)
eval (snd t)    γ = π₂ (eval t γ refl≤)
eval tt         γ = λ ξ → ∙
