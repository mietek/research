module BasicIPC.Metatheory.ClosedHilbert-BasicTarski where

open import BasicIPC.Syntax.ClosedHilbert public
open import BasicIPC.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation, for closed terms only.

eval₀ : ∀ {A} → ⊢ A → ⊨ A
eval₀ (app t u) = eval₀ t $ eval₀ u
eval₀ ci        = I
eval₀ ck        = K
eval₀ cs        = S
eval₀ cpair     = _,_
eval₀ cfst      = π₁
eval₀ csnd      = π₂
eval₀ tt        = ∙


-- Correctness of evaluation with respect to conversion.

eval₀✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval₀ t ≡ eval₀ t′
eval₀✓ refl⋙           = refl
eval₀✓ (trans⋙ p q)    = trans (eval₀✓ p) (eval₀✓ q)
eval₀✓ (sym⋙ p)        = sym (eval₀✓ p)
eval₀✓ (congapp⋙ p q)  = cong² _$_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congi⋙ p)      = cong I (eval₀✓ p)
eval₀✓ (congk⋙ p q)    = cong² K (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congs⋙ p q r)  = cong³ S (eval₀✓ p) (eval₀✓ q) (eval₀✓ r)
eval₀✓ (congpair⋙ p q) = cong² _,_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congfst⋙ p)    = cong π₁ (eval₀✓ p)
eval₀✓ (congsnd⋙ p)    = cong π₂ (eval₀✓ p)
eval₀✓ beta▻ₖ⋙         = refl
eval₀✓ beta▻ₛ⋙         = refl
eval₀✓ beta∧₁⋙         = refl
eval₀✓ beta∧₂⋙         = refl
eval₀✓ eta∧⋙           = refl
eval₀✓ eta⊤⋙          = refl
