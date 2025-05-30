{-# OPTIONS --sized-types #-}

module A201607.IPC.Metatheory.Hilbert-BasicTarski where

open import A201607.IPC.Syntax.Hilbert public
open import A201607.IPC.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = (eval t γ) (eval u γ)
eval ci        γ = I
eval ck        γ = K
eval cs        γ = S
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval unit      γ = ∙
eval cboom     γ = elim𝟘
eval cinl      γ = ι₁
eval cinr      γ = ι₂
eval ccase     γ = elim⊎


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                         = refl
eval✓ (trans⋙ p q)                  = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                      = sym (eval✓ p)
eval✓ (congapp⋙ {A} {B} p q)        = cong² (_⟦$⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)                    = cong I (eval✓ p)
eval✓ (congk⋙ p q)                  = cong² K (eval✓ p) (eval✓ q)
eval✓ (congs⋙ {A} {B} {C} p q r)    = cong³ (⟦S⟧ {A} {B} {C}) (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ {A} {B} p q)       = cong² (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)          = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)          = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ (congboom⋙ {C} p)             = cong (⟦elim𝟘⟧ {C}) (eval✓ p)
eval✓ (conginl⋙ {A} {B} p)          = cong (⟦ι₁⟧ {A} {B}) (eval✓ p)
eval✓ (conginr⋙ {A} {B} p)          = cong (⟦ι₂⟧ {A} {B}) (eval✓ p)
eval✓ (congcase⋙ {A} {B} {C} p q r) = cong³ (⟦celim⊎⟧ {A} {B} {C}) (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ beta▻ₖ⋙                       = refl
eval✓ beta▻ₛ⋙                       = refl
eval✓ beta∧₁⋙                       = refl
eval✓ beta∧₂⋙                       = refl
eval✓ eta∧⋙                         = refl
eval✓ eta⊤⋙                        = refl
eval✓ beta∨₁⋙                       = refl
eval✓ beta∨₂⋙                       = refl
