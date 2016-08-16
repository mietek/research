module BasicIS4.Metatheory.OpenGentzen-TarskiGabbayNanevskiMk1 where

open import BasicIS4.Syntax.OpenGentzen public
open import BasicIS4.Semantics.TarskiGabbayNanevskiMk1 public

open SyntacticComponent (λ Δ → □⋆ Δ ⊢_) public


-- Soundness with respect to all models, or evaluation.

-- FIXME: How to write this without translation?
postulate
  oops₁ : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⊨ A
  oops₂ : ∀ {A Δ Δ′} → □⋆ Δ ⊢ A → □⋆ Δ′ ⊢ A

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)             γ = lookup i γ
  eval (lam {A} {B} t)     γ = λ _ a → mono⊨ {B} bot⊆ (eval t (γ , oops₁ {A} a))
  eval (app t u)           γ = (eval t γ) bot⊆ (eval u γ)
  eval (multibox {A} ts u) γ = λ _ → oops₂ u , mono⊨ {A} bot⊆ (eval u (eval⋆ ts γ))
  eval (down t)            γ = let s , a = (eval t γ) refl⊆
                               in  a
  eval (pair t u)          γ = eval t γ , eval u γ
  eval (fst t)             γ = π₁ (eval t γ)
  eval (snd t)             γ = π₂ (eval t γ)
  eval tt                  γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊨⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
