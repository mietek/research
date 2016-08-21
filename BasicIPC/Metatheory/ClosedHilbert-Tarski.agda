module BasicIPC.Metatheory.ClosedHilbert-Tarski where

open import BasicIPC.Syntax.ClosedHilbert public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t $ eval u
eval ci        = id
eval ck        = const
eval cs        = ap
eval cpair     = _,_
eval cfst      = π₁
eval csnd      = π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙           = refl
eval✓ (trans⋙ p q)    = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)        = sym (eval✓ p)
eval✓ (congapp⋙ p q)  = cong₂ _$_ (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)      = cong id (eval✓ p)
eval✓ (congk⋙ p q)    = cong₂ const (eval✓ p) (eval✓ q)
eval✓ (congs⋙ p q r)  = cong₃ ap (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ p q) = cong₂ _,_ (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ p)    = cong π₁ (eval✓ p)
eval✓ (congsnd⋙ p)    = cong π₂ (eval✓ p)
eval✓ beta▻ₖ⋙         = refl
eval✓ beta▻ₛ⋙         = refl
eval✓ beta∧₁⋙         = refl
eval✓ beta∧₂⋙         = refl
eval✓ eta∧⋙           = refl
eval✓ eta⊤⋙          = refl
