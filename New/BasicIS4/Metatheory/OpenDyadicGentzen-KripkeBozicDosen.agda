module New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeBozicDosen where

open import New.BasicIS4.Syntax.OpenDyadicGentzen public
open import New.BasicIS4.Semantics.KripkeBozicDosen public


eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ζ →
                       let _ , (ζ′ , ξ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                       in  mono⊩⋆ ξ′ (δ ζ′))
eval (app t u)   γ δ = (eval t γ δ refl≤) (eval u γ δ)
eval (mvar i)    γ δ = lookup i (δ reflR)
eval (box t)     γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
eval (unbox t u) γ δ = eval u γ (λ ζ → δ ζ , (eval t γ δ) ζ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙
