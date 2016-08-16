module BasicIS4.Metatheory.Hilbert-KripkeOno where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.KripkeOno public


eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval (var i)          γ = lookup i γ
eval (app t u)        γ = (eval t γ refl≤) (eval u γ)
eval ci               γ = λ _ a → a
eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                          let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                              b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                          in  h b
eval (box t)          γ = λ ζ → eval t ∙
eval cdist            γ = λ _ □f ξ □a ζ →
                          let ζ′ = ≤⨾R→R (_ , (ξ , ζ))
                              f  = □f ζ′ refl≤
                              a  = □a ζ
                          in  f a
eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
eval cdown            γ = λ _ □a → □a reflR
eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
eval cfst             γ = λ _ s → π₁ s
eval csnd             γ = λ _ s → π₂ s
eval tt               γ = ∙
