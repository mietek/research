module New.BasicIS4.Metatheory.OpenDyadicGentzen-TarskiGabbayNanevskiMk1 where

open import New.BasicIS4.Syntax.OpenDyadicGentzen public
open import New.BasicIS4.Semantics.TarskiGabbayNanevskiMk1 public

open SyntacticComponent (λ Δ → ⌀ ⁏ Δ ⊢_) public


-- Soundness with respect to all models, or evaluation.

-- FIXME: How to write this without translation?
postulate
  oops₁ : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⊨ A
  oops₂ : ∀ {{_ : Model}} {C A Δ} → Δ , A ⊨ C → Δ ⊨ C

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval (var {A} i)         γ δ = mono⊨ {A} bot⊆ (lookup i γ)
eval (lam {A} {B} t)     γ δ = λ θ a → mono⊨ {B} θ (eval t (γ , oops₁ {A} a) δ)
eval (app t u)           γ δ = (eval t γ δ) refl⊆ (eval u γ δ)
eval (mvar {A} i)        γ δ = mono⊨ {A} bot⊆ (lookup i δ)
eval (box {A} t)         γ δ = λ θ → mmono⊢ θ t , mono⊨ {A} θ (eval t ∙ δ)
eval (unbox {A} {C} t u) γ δ = let s , a = (eval t γ δ) refl⊆
                               in  oops₂ {C} (eval u γ (δ , oops₁ {A} a))
eval (pair t u)          γ δ = eval t γ δ , eval u γ δ
eval (fst t)             γ δ = π₁ (eval t γ δ)
eval (snd t)             γ δ = π₂ (eval t γ δ)
eval tt                  γ δ = ∙

-- FIXME: Should we be using substitution in the unbox case everywhere?
{-# TERMINATING #-}
eval′ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval′ (var {A} i)         γ δ = mono⊨ {A} bot⊆ (lookup i γ)
eval′ (lam {A} {B} t)     γ δ = λ θ a → mono⊨ {B} θ (eval′ t (γ , oops₁ {A} a) δ)
eval′ (app t u)           γ δ = (eval′ t γ δ) refl⊆ (eval′ u γ δ)
eval′ (mvar {A} i)        γ δ = mono⊨ {A} bot⊆ (lookup i δ)
eval′ (box {A} t)         γ δ = λ θ → mmono⊢ θ t , mono⊨ {A} θ (eval′ t ∙ δ)
eval′ (unbox {A} {C} t u) γ δ = let s , a = eval′ t γ δ refl⊆
                                in  eval′ (m[ top ≔ s ] u) γ δ
eval′ (pair t u)          γ δ = eval′ t γ δ , eval′ u γ δ
eval′ (fst t)             γ δ = π₁ (eval′ t γ δ)
eval′ (snd t)             γ δ = π₂ (eval′ t γ δ)
eval′ tt                  γ δ = ∙
