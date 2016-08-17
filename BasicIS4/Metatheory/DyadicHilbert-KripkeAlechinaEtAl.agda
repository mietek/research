module BasicIS4.Metatheory.DyadicHilbert-KripkeAlechinaEtAl where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.KripkeAlechinaEtAl public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → ∀ᴹʷ⊩ Γ ⁏ Δ ⇒ A
eval (var i)          γ δ = lookup i γ
eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
eval ci               γ δ = λ _ a → a
eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                            in  h b
eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
eval (box t)          γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                            in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
eval cdown            γ δ = λ _ □a → □a refl≤ reflR
eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
eval cfst             γ δ = λ _ s → π₁ s
eval csnd             γ δ = λ _ s → π₂ s
eval tt               γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
