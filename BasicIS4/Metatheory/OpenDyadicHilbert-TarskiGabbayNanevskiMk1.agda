module BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevskiMk1 where

open import BasicIS4.Syntax.OpenDyadicHilbert public
open import BasicIS4.Semantics.TarskiGabbayNanevskiMk1 public

open SyntacticComponent (λ Δ → ⌀ ⁏ Δ ⊢_) public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval (var {A} i)      γ δ = mono⊨ {A} bot⊆ (lookup i γ)
eval (app t u)        γ δ = (eval t γ δ) refl⊆ (eval u γ δ)
eval ci               γ δ = λ _ → id
eval (ck {A})         γ δ = λ _ a θ b → mono⊨ {A} θ a
eval (cs {A} {B} {C}) γ δ = λ _ f θ g θ′ a →
                            let h = ((mono⊨ {A ▻ B ▻ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                                b = (mono⊨ {A ▻ B} θ′ g) refl⊆ a
                            in  h b
eval (mvar {A} i)     γ δ = mono⊨ {A} bot⊆ (lookup i δ)
eval (box {A} t)      γ δ = λ θ → mmono⊢ θ t , mono⊨ {A} θ (eval t ∙ δ)
eval cdist            γ δ = λ _ □f θ □a θ′ →
                            let t , f = □f (trans⊆ θ θ′)
                                u , a = □a θ′
                            in  app t u , f refl⊆ a
eval (cup {A})        γ δ = λ _ □a θ →
                            let t , a = □a θ
                            in  box t , (λ θ′ → mmono⊢ θ′ t , mono⊨ {A} θ′ a)
eval cdown            γ δ = λ _ □a →
                            let t , a = □a refl⊆
                            in  a
eval (cpair {A})      γ δ = λ _ a θ b → mono⊨ {A} θ a , b
eval cfst             γ δ = λ _ → π₁
eval csnd             γ δ = λ _ → π₂
eval tt               γ δ = ∙
