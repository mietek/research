module BasicIS4.Metatheory.Hilbert-TarskiGabbayNanevskiMk1 where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiGabbayNanevskiMk1 public

open SyntacticComponent (λ Δ → □⋆ Δ ⊢_) public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)          γ = lookup i γ
eval (app t u)        γ = (eval t γ refl⊆) (eval u γ)
eval ci               γ = λ _ → id
eval (ck {A})         γ = λ _ a θ b → mono⊨ {A} θ a
eval (cs {A} {B} {C}) γ = λ _ f θ g θ′ a →
                          let h = ((mono⊨ {A ▻ B ▻ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                              b = (mono⊨ {A ▻ B} θ′ g) refl⊆ a
                          in  h b
eval (box {A} t)      γ = λ θ₀ → mono⊢ (lift⊆ θ₀) t , mono⊨ {A} bot⊆ (eval t ∙)
eval cdist            γ = λ _ □f θ □a θ′ →
                          let t , f = □f (trans⊆ θ θ′)
                              u , a = □a θ′
                          in  app t u , f refl⊆ a
eval (cup {A})        γ = λ _ □a θ →
                          let t , a = □a θ
                          in  cxdown (lift t) , (λ θ′ →
                                mono⊢ (lift⊆ θ′) t , mono⊨ {A} θ′ a)
eval cdown            γ = λ _ □a →
                          let t , a = □a refl⊆
                          in  a
eval (cpair {A})      γ = λ _ a θ b → mono⊨ {A} θ a , b
eval cfst             γ = λ _ → π₁
eval csnd             γ = λ _ → π₂
eval tt               γ = ∙
