module BasicIS4.DualContext.Gentzen.KripkeSoundness where

open import BasicIS4.DualContext.Gentzen public


module Ono where
  open import BasicIS4.KripkeSemantics.Ono public
  open StandardForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ζ → δ (transR (≤→R ξ) ζ))
  eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i (δ reflR)
  eval (box t)     γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval (unbox t u) γ δ = eval u γ (λ ζ → δ ζ , (eval t γ δ) ζ)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙

module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public
  open StandardForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ζ →
                         let _ , (ζ′ , ξ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                         in  mono⊩⋆ ξ′ (δ ζ′))
  eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i (δ reflR)
  eval (box t)     γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval (unbox t u) γ δ = eval u γ (λ ζ → δ ζ , (eval t γ δ) ζ)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙

module Wijesekera where
  open import BasicIS4.KripkeSemantics.Wijesekera public
  open StandardForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ξ′ ζ → δ (trans≤ ξ ξ′) ζ)
  eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i (δ refl≤ reflR)
  eval (box t)     γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                         let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                         in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval (unbox t u) γ δ = eval u γ (λ ξ ζ → δ ξ ζ , (eval t γ δ) ξ ζ)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙

module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public
  open StandardForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ξ′ ζ → δ (trans≤ ξ ξ′) ζ)
  eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i (δ refl≤ reflR)
  eval (box t)     γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                         let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                         in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval (unbox t u) γ δ = eval u γ (λ ξ ζ → δ ξ ζ , (eval t γ δ) ξ ζ)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙

module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public
  open StandardForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ξ′ ζ → δ (trans≤ ξ ξ′) ζ)
  eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i (δ refl≤ reflR)
  eval (box t)     γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                         let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                         in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval (unbox t u) γ δ = eval u γ (λ ξ ζ → δ ξ ζ , (eval t γ δ) ξ ζ)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙
