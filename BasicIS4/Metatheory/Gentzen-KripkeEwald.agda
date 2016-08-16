module BasicIS4.Metatheory.Gentzen-KripkeEwald where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.KripkeEwald public


mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app t u)       γ = (eval t γ refl≤) (eval u γ)
  eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
  eval (down t)        γ = eval t γ refl≤ reflR
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
  eval⋆ {⌀}     ∙        γ ξ ζ = ∙
  eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
                                 let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                                 in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)
