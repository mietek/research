module A201607.BasicT.Metatheory.Gentzen-BasicTarski where

open import A201607.BasicT.Syntax.Gentzen public
open import A201607.BasicT.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)     γ = lookup i γ
eval (lam t)     γ = λ a → eval t (γ , a)
eval (app t u)   γ = eval t γ $ eval u γ
eval (pair t u)  γ = eval t γ , eval u γ
eval (fst t)     γ = π₁ (eval t γ)
eval (snd t)     γ = π₂ (eval t γ)
eval unit        γ = ∙
eval true        γ = true
eval false       γ = false
eval (if t u v)  γ = ifᴮ (eval t γ) (eval u γ) (eval v γ)
eval zero        γ = zero
eval (suc t)     γ = suc (eval t γ)
eval (it t u v)  γ = itᴺ (eval t γ) (eval u γ) (eval v γ)
eval (rec t u v) γ = recᴺ (eval t γ) (eval u γ) (eval v γ)


-- TODO: Correctness of evaluation with respect to conversion.
