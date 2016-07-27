module IPC.Hilbert.Nested.KripkeSoundness where

open import IPC.KripkeSemantics public
open import IPC.Hilbert.Nested public


-- FIXME: Add more CPS combinators.
postulate
  oops : ∀ {A : Set} → A


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)             γ = lookup i γ
eval (app {A} {B} t u)   γ = bind {A ▷ B} {B} (eval t γ)
                               (λ ξ f → f refl≤ (mono⊩ {A} ξ (eval u γ)))
eval (ci {A})            γ = return {A ▷ A} (λ _ a → a)
eval (ck {A} {B})        γ = return {A ▷ B ▷ A} (λ _ a →
                             return {B ▷ A} (λ ξ b → mono⊩ {A} ξ a))
eval (cs {A} {B} {C})    γ = return {(A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C} (λ _ f →
                             return {(A ▷ B) ▷ A ▷ C} (λ ξ g →
                             return {A ▷ C} (λ ξ′ t →
                             let f′ = mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f
                                 g′ = mono⊩ {A ▷ B} ξ′ g
                             in  bind {A} {C} t (λ ξ″ a →
                                 oops))))
eval (cpair {A} {B})     γ = return {A ▷ B ▷ A ∧ B} (λ _ a →
                             return {B ▷ A ∧ B} (λ ξ b →
                             return {A ∧ B} (mono⊩ {A} ξ a , b)))
eval (cfst {A} {B})      γ = return {A ∧ B ▷ A} (λ _ t →
                             bind {A ∧ B} {A} t (λ _ s → π₁ s))
eval (csnd {A} {B})      γ = return {A ∧ B ▷ B} (λ _ t →
                             bind {A ∧ B} {B} t (λ _ s → π₂ s))
eval tt                  γ = return {⊤} ∙
eval (cboom {C})         γ = return {⊥ ▷ C} (λ _ t →
                             bind {⊥} {C} t (λ ξ s → elimBot s))
eval (cinl {A} {B})      γ = return {A ▷ A ∨ B} (λ _ a →
                             return {A ∨ B} (ι₁ a))
eval (cinr {A} {B})      γ = return {B ▷ A ∨ B} (λ _ b →
                             return {A ∨ B} (ι₂ b))
eval (ccase {A} {B} {C}) γ = return {A ∨ B ▷ (A ▷ C) ▷ (B ▷ C) ▷ C} (λ _ t →
                             return {(A ▷ C) ▷ (B ▷ C) ▷ C} (λ ξ u →
                             return {(B ▷ C) ▷ C} (λ ξ′ v →
                             let t′ = mono⊩ {A ∨ B} (trans≤ ξ ξ′) t
                                 u′ = mono⊩ {A ▷ C} ξ′ u
                             in  bind {A ∨ B} {C} t′ (λ ξ″ s →
                                 let u″ = mono⊩ {A ▷ C} ξ″ u′
                                     v″ = mono⊩ {B ▷ C} ξ″ v
                                 in κ s (λ a → oops)
                                        (λ b → oops)))))
