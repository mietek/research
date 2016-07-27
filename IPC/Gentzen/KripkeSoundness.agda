module IPC.Gentzen.KripkeSoundness where

open import IPC.KripkeSemantics public
open import IPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)                  γ = lookup i γ
eval (lam {A} {B} t)          γ = return {A ▷ B} (λ ξ a → eval t (mono⊩⋆ ξ γ , a))
eval (app {A} {B} t u)        γ = bind {A ▷ B} {B} (eval t γ)
                                    (λ ξ f → f refl≤ (eval u (mono⊩⋆ ξ γ)))
eval (pair {A} {B} t u)       γ = return {A ∧ B} (eval t γ , eval u γ)
eval (fst {A} {B} t)          γ = bind {A ∧ B} {A} (eval t γ) (λ ξ s → π₁ s)
eval (snd {A} {B} t)          γ = bind {A ∧ B} {B} (eval t γ) (λ ξ s → π₂ s)
eval tt                       γ = return {⊤} ∙
eval (boom {C} t)             γ = bind {⊥} {C} (eval t γ) (λ ξ s → elimBot s)
eval (inl {A} {B} t)          γ = return {A ∨ B} (ι₁ (eval t γ))
eval (inr {A} {B} t)          γ = return {A ∨ B} (ι₂ (eval t γ))
eval (case {A} {B} {C} t u v) γ = bind {A ∨ B} {C} (eval t γ) (λ ξ s → κ s
                                    (λ a → eval u (mono⊩⋆ ξ γ , λ ξ′ k → a ξ′ k))
                                    (λ b → eval v (mono⊩⋆ ξ γ , λ ξ′ k → b ξ′ k)))

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
