module BasicIS4.Metatheory.Hilbert-BasicKripkeBozicDosen where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.BasicKripkeBozicDosen public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval ci                γ = K I
eval (ck {A} {B})      γ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ = K (⟪S⟫′ {A} {B} {C})
eval (box t)           γ = λ ζ → eval t ∙
eval (cdist {A} {B})   γ = K (_⟪D⟫′_ {A} {B})
eval (cup {A})         γ = K (⟪↑⟫ {A})
eval (cdown {A})       γ = K (⟪↓⟫ {A})
eval (cpair {A} {B})   γ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ = K π₁
eval csnd              γ = K π₂
eval tt                γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
