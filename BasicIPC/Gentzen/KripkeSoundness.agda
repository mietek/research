module BasicIPC.Gentzen.KripkeSoundness where

open import BasicIPC.Gentzen public
open import BasicIPC.KripkeSemantics public




-- Using forcing based on the Gödel translation of IPC to S4.

module GodelSoundness where
  open GodelSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)    γ = lookup i γ
  eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
  eval (pair t u) γ = λ ξ → let γ′ = mono⊩⋆ ξ γ
                             in  eval t γ′ , eval u γ′
  eval (fst t)    γ = π₁ (eval t γ refl≤)
  eval (snd t)    γ = π₂ (eval t γ refl≤)
  eval tt         γ = λ ξ → ∙





-- Using forcing based on the McKinsey-Tarski translation of IPC to S4.

module McKinseyTarskiSoundness where
  open McKinseyTarskiSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)    γ = lookup i γ
  eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
  eval (pair t u) γ = eval t γ , eval u γ
  eval (fst t)    γ = π₁ (eval t γ)
  eval (snd t)    γ = π₂ (eval t γ)
  eval tt         γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
