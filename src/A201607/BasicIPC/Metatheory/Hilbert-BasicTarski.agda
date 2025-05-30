{-# OPTIONS --sized-types #-}

module A201607.BasicIPC.Metatheory.Hilbert-BasicTarski where

open import A201607.BasicIPC.Syntax.Hilbert public
open import A201607.BasicIPC.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ $ eval u γ
eval ci        γ = I
eval ck        γ = K
eval cs        γ = S
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval unit      γ = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                      = refl
eval✓ (trans⋙ p q)               = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                   = sym (eval✓ p)
eval✓ (congapp⋙ {A} {B} p q)     = cong² (_⟦$⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)                 = cong I (eval✓ p)
eval✓ (congk⋙ p q)               = cong² K (eval✓ p) (eval✓ q)
eval✓ (congs⋙ {A} {B} {C} p q r) = cong³ (⟦S⟧ {A} {B} {C}) (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ {A} {B} p q)    = cong² (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)       = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)       = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ beta▻ₖ⋙                    = refl
eval✓ beta▻ₛ⋙                    = refl
eval✓ beta∧₁⋙                    = refl
eval✓ beta∧₂⋙                    = refl
eval✓ eta∧⋙                      = refl
eval✓ eta⊤⋙                     = refl
