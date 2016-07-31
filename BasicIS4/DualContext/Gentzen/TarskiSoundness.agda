module BasicIS4.DualContext.Gentzen.TarskiSoundness where

open import BasicIS4.DualContext.Gentzen public
open import BasicIS4.TarskiSemantics public

import BasicIS4.DualContext.Hilbert.Nested.TarskiSoundness as HN
import BasicIS4.DualContext.Translation as T


module Closed where
  open TruthWithClosedBox (ClosedBox) public
  open T
  open T.Closed

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval {A} t γ δ = hn⇒g {A} (HN.Closed.eval (g→hn t) (g⇒hn⋆ γ) (g⇒hn⋆ δ))

  -- FIXME: How to write this without translation?
  postulate
    oops : ∀ {A Δ} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ⌀ ⊢ A

  eval′ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval′ (var i)     γ δ = lookup i γ
  eval′ (lam t)     γ δ = λ a → eval′ t (γ , a) δ
  eval′ (app t u)   γ δ = (eval′ t γ δ) (eval′ u γ δ)
  eval′ (mvar i)    γ δ = lookup i δ
  eval′ (box t)     γ δ = [ oops t ] , eval′ t ∙ δ
  eval′ (unbox t u) γ δ = let [ s ] , a = eval′ t γ δ
                         in  eval′ u γ (δ , a)
  eval′ (pair t u)  γ δ = eval′ t γ δ , eval′ u γ δ
  eval′ (fst t)     γ δ = π₁ (eval′ t γ δ)
  eval′ (snd t)     γ δ = π₂ (eval′ t γ δ)
  eval′ tt          γ δ = ∙


module Strange where
  open TruthWithClosedBox (StrangeBox) public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ a → eval t (γ , a) δ
  eval (app t u)   γ δ = (eval t γ δ) (eval u γ δ)
  eval (mvar i)    γ δ = lookup i δ
  eval (box t)     γ δ = [ t ] , eval t ∙ δ
  eval (unbox t u) γ δ = let [ s ] , a = eval t γ δ
                         in  eval u γ (δ , a)
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙


module Open where
  open TruthWithOpenBox (OpenBox) public
  open T
  open T.Open

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval {A} t γ δ = hn⇒g {A} (HN.Open.eval (g→hn t) (g⇒hn⋆ γ) (g⇒hn⋆ δ))

  -- FIXME: How to write this without translation?
  postulate
    oops₁ : ∀ {A Δ} {{_ : Model}} → Δ ⊨ A → ⌀ ⊨ A
    oops₂ : ∀ {C A Δ} {{_ : Model}} → Δ , A ⊨ C → Δ ⊨ C

  eval′ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval′ (var {A} i)         γ δ = mono⊨ {A} bot⊆ (lookup i γ)
  eval′ (lam {A} {B} t)     γ δ = λ θ a → mono⊨ {B} θ (eval′ t (γ , oops₁ {A} a) δ)
  eval′ (app t u)           γ δ = (eval′ t γ δ) refl⊆ (eval′ u γ δ)
  eval′ (mvar {A} i)        γ δ = mono⊨ {A} bot⊆ (lookup i δ)
  eval′ (box {A} t)         γ δ = λ θ → [ mmono⊢ θ t ] , mono⊨ {A} θ (eval′ t ∙ δ)
  eval′ (unbox {A} {C} t u) γ δ = let [ s ] , a = eval′ t γ δ refl⊆
                                 in  oops₂ {C} (eval′ u γ (δ , oops₁ {A} a))
                                 --in  eval′ (m[ top ≔ s ] u) γ δ
  eval′ (pair t u)          γ δ = eval′ t γ δ , eval′ u γ δ
  eval′ (fst t)             γ δ = π₁ (eval′ t γ δ)
  eval′ (snd t)             γ δ = π₂ (eval′ t γ δ)
  eval′ tt                  γ δ = ∙

  -- FIXME: Should we be using substitution in the unbox case everywhere?
  {-# TERMINATING #-}
  eval″ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval″ (var {A} i)         γ δ = mono⊨ {A} bot⊆ (lookup i γ)
  eval″ (lam {A} {B} t)     γ δ = λ θ a → mono⊨ {B} θ (eval″ t (γ , oops₁ {A} a) δ)
  eval″ (app t u)           γ δ = (eval″ t γ δ) refl⊆ (eval″ u γ δ)
  eval″ (mvar {A} i)        γ δ = mono⊨ {A} bot⊆ (lookup i δ)
  eval″ (box {A} t)         γ δ = λ θ → [ mmono⊢ θ t ] , mono⊨ {A} θ (eval″ t ∙ δ)
  eval″ (unbox {A} {C} t u) γ δ = let [ s ] , a = eval″ t γ δ refl⊆
                                 in  eval″ (m[ top ≔ s ] u) γ δ
  eval″ (pair t u)          γ δ = eval″ t γ δ , eval″ u γ δ
  eval″ (fst t)             γ δ = π₁ (eval″ t γ δ)
  eval″ (snd t)             γ δ = π₂ (eval″ t γ δ)
  eval″ tt                  γ δ = ∙
