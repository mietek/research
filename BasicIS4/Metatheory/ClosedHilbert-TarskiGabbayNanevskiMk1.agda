module BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevskiMk1 where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Syntax.ClosedHilbertTranslatedEquipment public
open import BasicIS4.Semantics.TarskiGabbayNanevskiMk1 public

open SyntacticComponent (λ Δ A → ⊢ □⋆ Δ ▻⋯▻ A) public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u)        = (eval t) refl⊆ (eval u)
eval ci               = λ _ → id
eval (ck {A})         = λ _ a θ b → mono⊨ {A} θ a
eval (cs {A} {B} {C}) = λ _ f θ g θ′ a →
                        let h = ((mono⊨ {A ▻ B ▻ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                            b = (mono⊨ {A ▻ B} θ′ g) refl⊆ a
                        in  h b
eval (box {A} t)      = λ θ₀ → ᵀml θ₀ t , mono⊨ {A} bot⊆ (eval t)
eval cdist            = λ _ □f θ □a {Δ′} θ′ →
                        let t , f = □f (trans⊆ θ θ′)
                            u , a = □a θ′
                        in  ᵀapp {□⋆ Δ′} t u , f refl⊆ a
eval (cup {A})        = λ _ □a {Δ′} θ →
                        let t , a = □a θ
                        in  ᵀcxdown {Δ′} (ᵀlift {□⋆ Δ′} t) , (λ θ′ →
                              ᵀml θ′ t , mono⊨ {A} θ′ a)
eval cdown            = λ _ □a →
                        let t , a = □a refl⊆
                        in  a
eval (cpair {A})      = λ _ a θ b → mono⊨ {A} θ a , b
eval cfst             = λ _ → π₁
eval csnd             = λ _ → π₂
eval tt               = ∙
