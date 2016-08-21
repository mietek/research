module BasicIPC.Metatheory.Gentzen-BasicTarski where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (γ , a)
eval (app t u)  γ = eval t γ $ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


-- Correctness of evaluation with respect to conversion.

-- FIXME: How to show this?
postulate
  oops₁ : ∀ {{_ : Model}} {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
          → eval ([ top ≔ u ] t) ≡ (λ γ → eval t (γ , eval u γ))
  oops₂ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ▻ B}
          → eval t ≡ (λ γ a → eval (mono⊢ (weak⊆ {A = A}) t) (γ , a) a)

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                    = refl
eval✓ (trans⋙ p q)             = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                 = sym (eval✓ p)
eval✓ (conglam⋙ {A} {B} p)     = cong (⟦λ⟧ {A} {B}) (eval✓ p)
eval✓ (congapp⋙ {A} {B} p q)   = cong² (_⟦$⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congpair⋙ {A} {B} p q)  = cong² (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)     = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)     = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ (beta▻⋙ {A} {B} {t} {u}) = sym (oops₁ {A} {B} {_} {t} {u})
eval✓ (eta▻⋙ {A} {B} {t})      = oops₂ {A} {B} {_} {t}
eval✓ beta∧₁⋙                  = refl
eval✓ beta∧₂⋙                  = refl
eval✓ eta∧⋙                    = refl
eval✓ eta⊤⋙                   = refl
