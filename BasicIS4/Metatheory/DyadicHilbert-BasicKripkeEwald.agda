module A201607.BasicIS4.Metatheory.DyadicHilbert-BasicKripkeEwald where

open import A201607.BasicIS4.Syntax.DyadicHilbert public
open import A201607.BasicIS4.Semantics.BasicKripkeEwald public hiding (_⊨_) -- TODO


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval ci                γ δ = K I
eval (ck {A} {B})      γ δ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ δ = K (⟪S⟫′ {A} {B} {C})
eval (mvar i)          γ δ = lookup i (δ refl≤ reflR)
eval (box {A} t)       γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                               let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                               in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
eval (cdist {A} {B})   γ δ = K (_⟪D⟫′_ {A} {B})
eval (cup {A})         γ δ = K (⟪↑⟫ {A})
eval (cdown {A})       γ δ = K (⟪↓⟫ {A})
eval (cpair {A} {B})   γ δ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ δ = K π₁
eval csnd              γ δ = K π₂
eval unit              γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
