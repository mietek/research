module BasicIS4.Metatheory.OpenGentzen-KripkeBozicDosen where

open import BasicIS4.Syntax.OpenGentzen public
open import BasicIS4.Semantics.KripkeBozicDosen public


mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)       γ = (eval t γ refl≤) (eval u γ)
  eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
  eval (down t)        γ = eval t γ reflR
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
  eval⋆ {⌀}     ∙        γ ζ = ∙
  eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)
