module BasicIS4.Metatheory.DyadicGentzen-BasicKripkeAlechina where

open import BasicIS4.Syntax.DyadicGentzen public
open import BasicIS4.Semantics.BasicKripkeAlechina public hiding (_⊨_) -- TODO


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (lam t)           γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ξ′ ζ →
                               δ (trans≤ ξ ξ′) ζ)
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval (mvar i)          γ δ = lookup i (δ refl≤ reflR)
eval (box t)           γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                               let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                               in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
eval (unbox t u)       γ δ = eval u γ (λ ξ ζ → δ ξ ζ , (eval t γ δ) ξ ζ)
eval (pair t u)        γ δ = eval t γ δ , eval u γ δ
eval (fst t)           γ δ = π₁ (eval t γ δ)
eval (snd t)           γ δ = π₂ (eval t γ δ)
eval unit              γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
