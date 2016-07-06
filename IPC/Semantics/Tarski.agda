module IPC.Semantics.Tarski where

open import IPC.Gentzen public


-- Tarski models.

record Model : Set₁ where
  field
    ⊨ᵃ_ : Atom → Set

open Model {{…}} public


-- Truth in a model.

module _ {{_ : Model}} where
  ⊨ᵗ_ : Ty → Set
  ⊨ᵗ (α p)   = ⊨ᵃ p
  ⊨ᵗ (A ⊃ B) = ⊨ᵗ A → ⊨ᵗ B
  ⊨ᵗ ι       = ⊤
  ⊨ᵗ (A ∧ B) = ⊨ᵗ A × ⊨ᵗ B

  ⊨ᶜ_ : Cx Ty → Set
  ⊨ᶜ ⌀       = ⊤
  ⊨ᶜ (Γ , A) = ⊨ᶜ Γ × ⊨ᵗ A


-- Truth in all models.

_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊨ᶜ Γ → ⊨ᵗ A


-- Soundness with respect to all models.

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
