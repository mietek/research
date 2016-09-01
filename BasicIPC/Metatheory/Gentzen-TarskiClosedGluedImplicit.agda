module BasicIPC.Metatheory.Gentzen-TarskiClosedGluedImplicit where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiClosedGluedImplicit public

open ImplicitSyntax (∅ ⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ∅ ⊢ A
  reify {α P}   s = syn s
  reify {A ▻ B} s = syn s
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
  reify {⊤}    s = tt

  reify⋆ : ∀ {Ξ} → ⊩⋆ Ξ → ∅ ⊢⋆ Ξ
  reify⋆ {∅}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = multicut (reify⋆ γ) (lam t) ⅋ λ a →
                      eval t (γ , a)
eval (app t u)  γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { ⊩ᵅ_ = λ P → ∅ ⊢ α P
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ∅ ⊨ A → ∅ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ∅ ⊢ A → ∅ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
