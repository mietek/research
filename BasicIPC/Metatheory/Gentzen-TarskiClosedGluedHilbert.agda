module BasicIPC.Metatheory.Gentzen-TarskiClosedGluedHilbert where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiClosedGluedHilbert public

import BasicIPC.Metatheory.Hilbert-TarskiClosedGluedHilbert as H

open import BasicIPC.Syntax.Translation using (g→h)


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_]₀ : ∀ {A} → ⌀ ⊢ A → [⊢] A
  [ t ]₀ = H.[ g→h t ]₀


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = [multicut] (reifyʳ⋆ γ) [ lam⋆₀ t ]₀ , λ a →
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
      { ⊩ᵅ_    = λ P → ⌀ ⊢ α P
      ; [⊢]_   = ⌀ ⊢_
      ; [app]   = app
      ; [ci]    = ci
      ; [ck]    = ck
      ; [cs]    = cs
      ; [cpair] = cpair
      ; [cfst]  = cfst
      ; [csnd]  = csnd
      ; [tt]    = tt
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ⌀ ⊨ A → ⌀ ⊢ A
quot₀ t = reifyʳ (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
