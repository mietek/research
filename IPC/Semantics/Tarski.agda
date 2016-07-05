module IPC.Semantics.Tarski where

open import IPC.Gentzen public


-- Tarski models.

record Model : Set₁ where
  field
    ⊨ₐ_ : Atom → Set

open Model {{…}} public


-- Truth in a model.

module _ {{_ : Model}} where
  ⊨ₜ_ : Ty → Set
  ⊨ₜ (α p)    = ⊨ₐ p
  ⊨ₜ (A ⇒ B) = ⊨ₜ A → ⊨ₜ B
  ⊨ₜ ⊤       = Unit
  ⊨ₜ (A ∧ B)  = ⊨ₜ A × ⊨ₜ B
  ⊨ₜ (A ∨ B)  = ⊨ₜ A + ⊨ₜ B
  ⊨ₜ ⊥       = Empty

  ⊨ᵢ_ : Cx Ty → Set
  ⊨ᵢ ∅       = Unit
  ⊨ᵢ (Γ , A) = ⊨ᵢ Γ × ⊨ₜ A


-- Truth in all models.

_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊨ᵢ Γ → ⊨ₜ A


-- Soundness with respect to all models.

lookup : ∀ {Γ A} → A ∈ Γ → Γ ⊨ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
eval (var i)      γ = lookup i γ
eval (lam t)      γ = λ a → eval t (γ ∙ a)
eval (app t u)    γ = (eval t γ) (eval u γ)
eval unit         γ = τ
eval (pair t u)   γ = eval t γ ∙ eval u γ
eval (fst t)      γ with eval t γ
…                | a ∙ b = a
eval (snd t)      γ with eval t γ
…                | a ∙ b = b
eval (inl t)      γ = ι₁ (eval t γ)
eval (inr t)      γ = ι₂ (eval t γ)
eval (case t u v) γ with eval t γ
…                | ι₁ a = eval u (γ ∙ a)
…                | ι₂ b = eval v (γ ∙ b)
eval (boom t)     γ with eval t γ
…                | ()
