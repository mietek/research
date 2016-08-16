module BasicIS4.Metatheory.OpenHilbert-KripkeEwald where

open import BasicIS4.Syntax.OpenHilbert public
open import BasicIS4.Semantics.KripkeEwald public


eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)          γ = lookup i γ
eval (app t u)        γ = (eval t γ refl≤) (eval u γ)
eval ci               γ = λ _ a → a
eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                          let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                              b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                          in  h b
eval (box t)          γ = λ ξ ζ → eval t ∙
eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                          let f = □f (trans≤ ξ ξ′) ζ refl≤
                              a = □a ξ′ ζ
                          in  f a
eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                          let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                          in  □a ξ″ ζ″
eval cdown            γ = λ _ □a → □a refl≤ reflR
eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
eval cfst             γ = λ _ s → π₁ s
eval csnd             γ = λ _ s → π₂ s
eval tt               γ = ∙
