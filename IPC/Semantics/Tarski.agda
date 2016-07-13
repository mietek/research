module IPC.Semantics.Tarski where

open import IPC.Gentzen public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᴬ_
  field
    ⊨ᴬ_ : Atom → Set

open Model {{…}} public


-- Truth in one model.

module _ {{_ : Model}} where
  infix 3 ⊨ᵀ_
  ⊨ᵀ_ : Ty → Set
  ⊨ᵀ α p   = ⊨ᴬ p
  ⊨ᵀ A ⊃ B = ⊨ᵀ A → ⊨ᵀ B
  ⊨ᵀ ι     = ⊤
  ⊨ᵀ A ∧ B = ⊨ᵀ A × ⊨ᵀ B

  infix 3 ⊨ᴳ_
  ⊨ᴳ_ : Cx Ty → Set
  ⊨ᴳ ⌀     = ⊤
  ⊨ᴳ Γ , A = ⊨ᴳ Γ × ⊨ᵀ A


-- Truth in all models.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊨ᴳ Γ → ⊨ᵀ A


-- Soundness with respect to all models, or evaluation.

lookup : ∀ {Γ A} → A ∈ Γ → Γ ⊨ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (γ ∙ a)
eval (app t u)  γ = (eval t γ) (eval u γ)
eval unit       γ = tt
eval (pair t u) γ = eval t γ ∙ eval u γ
eval (fst t)    γ with eval t γ
…                | a ∙ b = a
eval (snd t)    γ with eval t γ
…                | a ∙ b = b
