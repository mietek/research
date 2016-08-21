module BasicIS4.Metatheory.Hilbert-BasicKripkeEwald where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.BasicKripkeEwald public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval ci                γ = const id
eval (ck {A} {B})      γ = const (⟪const⟫ {A} {B})
eval (cs {A} {B} {C})  γ = const (⟪ap⟫′ {A} {B} {C})
eval (box t)           γ = λ ξ ζ → eval t ∙
eval (cdist {A} {B})   γ = const (_⟪◎⟫′_ {A} {B})
eval (cup {A})         γ = const (⟪⇑⟫ {A})
eval (cdown {A})       γ = const (⟪⇓⟫ {A})
eval (cpair {A} {B})   γ = const (_⟪,⟫′_ {A} {B})
eval cfst              γ = const π₁
eval csnd              γ = const π₂
eval tt                γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
