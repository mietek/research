module BasicIS4.Metatheory.DyadicHilbert-BasicKripkeOno where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.BasicKripkeOno public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval ci                γ δ = const id
eval (ck {A} {B})      γ δ = const (⟪const⟫ {A} {B})
eval (cs {A} {B} {C})  γ δ = const (⟪ap⟫′ {A} {B} {C})
eval (mvar i)          γ δ = lookup i (δ reflR)
eval (box t)           γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
eval (cdist {A} {B})   γ δ = const (_⟪◎⟫′_ {A} {B})
eval (cup {A})         γ δ = const (⟪⇑⟫ {A})
eval (cdown {A})       γ δ = const (⟪⇓⟫ {A})
eval (cpair {A} {B})   γ δ = const (_⟪,⟫′_ {A} {B})
eval cfst              γ δ = const π₁
eval csnd              γ δ = const π₂
eval tt                γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.
