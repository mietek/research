{-# OPTIONS --sized-types #-}

module A201607.BasicIS4.Metatheory.DyadicGentzen-BasicKripkeBozicDosen where

open import A201607.BasicIS4.Syntax.DyadicGentzen public
open import A201607.BasicIS4.Semantics.BasicKripkeBozicDosen public hiding (_⊨_) -- TODO


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (lam t)           γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ζ →
                               let _ , (ζ′ , ξ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                               in  mono⊩⋆ ξ′ (δ ζ′))
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval (mvar i)          γ δ = lookup i (δ reflR)
eval (box t)           γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
eval (unbox t u)       γ δ = eval u γ (λ ζ → δ ζ , (eval t γ δ) ζ)
eval (pair t u)        γ δ = eval t γ δ , eval u γ δ
eval (fst t)           γ δ = π₁ (eval t γ δ)
eval (snd t)           γ δ = π₂ (eval t γ δ)
eval unit              γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
