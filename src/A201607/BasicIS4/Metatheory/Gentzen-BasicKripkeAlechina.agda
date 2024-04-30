module A201607.BasicIS4.Metatheory.Gentzen-BasicKripkeAlechina where

open import A201607.BasicIS4.Syntax.Gentzen public
open import A201607.BasicIS4.Semantics.BasicKripkeAlechina public


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)           γ = lookup i γ
  eval (lam t)           γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
  eval (multibox ts u)   γ = λ ξ ζ → eval u (thing ts γ ξ ζ)
  eval (down {A} t)      γ = ⟪↓⟫ {A} (eval t γ)
  eval (pair t u)        γ = eval t γ , eval u γ
  eval (fst t)           γ = π₁ (eval t γ)
  eval (snd t)           γ = π₂ (eval t γ)
  eval unit              γ = ∙

  -- TODO: What is this?
  thing : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′ : World} → w ≤ w′ → ∀ {v′ : World} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
  thing {∅}     ∙        γ ξ ζ = ∙
  thing {Δ , B} (ts , t) γ ξ ζ = thing ts γ ξ ζ , λ ξ′ ζ′ →
                                 let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                                 in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ = ∙
eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.
