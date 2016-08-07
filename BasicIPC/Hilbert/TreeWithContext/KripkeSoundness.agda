module BasicIPC.Hilbert.TreeWithContext.KripkeSoundness where

open import BasicIPC.Hilbert.TreeWithContext public




-- Using truth based on the Gödel translation of IPC to S4.

module GodelSoundness where
  open import BasicIPC.KripkeSemantics.Godel public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ → id
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                                g′ = mono⊩ {A ▻ B} ξ′ g
                            in  (f′ refl≤ a) refl≤ (g′ refl≤ a)
  eval (cpair {A} {B})  γ = λ _ a ξ b ξ′ → mono⊩ {A} (trans≤ ξ ξ′) a , mono⊩ {B} ξ′ b
  eval cfst             γ = λ _ s → π₁ (s refl≤)
  eval csnd             γ = λ _ s → π₂ (s refl≤)
  eval tt               γ = λ _ → ∙




-- Using truth based on the McKinsey-Tarski translation of IPC to S4.

module McKinseyTarskiSoundness where
  open import BasicIPC.KripkeSemantics.McKinseyTarski public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ → id
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                                g′ = mono⊩ {A ▻ B} ξ′ g
                            in  (f′ refl≤ a) refl≤ (g′ refl≤ a)
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙
