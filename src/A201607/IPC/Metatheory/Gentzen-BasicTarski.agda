module A201607.IPC.Metatheory.Gentzen-BasicTarski where

open import A201607.IPC.Syntax.Gentzen public
open import A201607.IPC.Semantics.BasicTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)      γ = lookup i γ
eval (lam t)      γ = λ a → eval t (γ , a)
eval (app t u)    γ = eval t γ $ eval u γ
eval (pair t u)   γ = eval t γ , eval u γ
eval (fst t)      γ = π₁ (eval t γ)
eval (snd t)      γ = π₂ (eval t γ)
eval unit         γ = ∙
eval (boom t)     γ = elim𝟘 (eval t γ)
eval (inl t)      γ = ι₁ (eval t γ)
eval (inr t)      γ = ι₂ (eval t γ)
eval (case t u v) γ = elim⊎ (eval t γ)
                        (λ a → eval u (γ , a))
                        (λ b → eval v (γ , b))


-- Correctness of evaluation with respect to conversion.

-- FIXME: How to show this?
postulate
  oops₁ : ∀ {{_ : Model}} {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
          → eval ([ top ≔ u ] t) ≡ (λ γ → eval t (γ , eval u γ))
  oops₂ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ▻ B}
          → eval t ≡ (λ γ a → eval (mono⊢ (weak⊆ {A = A}) t) (γ , a) a)
  oops₃ : ∀ {{_ : Model}} {A B C Γ} {t : Γ ⊢ A} {u : Γ , A ⊢ C} {v : Γ , B ⊢ C}
          → eval ([ top ≔ t ] u) ≡ (λ γ → eval u (γ , eval t γ))
  oops₄ : ∀ {{_ : Model}} {A B C Γ} {t : Γ ⊢ B} {u : Γ , A ⊢ C} {v : Γ , B ⊢ C}
          → eval ([ top ≔ t ] v) ≡ (λ γ → eval v (γ , eval t γ))
  oops₅ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ∨ B}
          → eval t ≡ (λ γ → elim⊎ (eval t γ) (λ a → ι₁ a) (λ b → ι₂ b))

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                             = refl
eval✓ (trans⋙ p q)                      = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                          = sym (eval✓ p)
eval✓ (conglam⋙ {A} {B} p)              = cong (⟦λ⟧ {A} {B}) (eval✓ p)
eval✓ (congapp⋙ {A} {B} p q)            = cong² (_⟦$⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congpair⋙ {A} {B} p q)           = cong² (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)              = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)              = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ (congboom⋙ {C} p)                 = cong (⟦elim𝟘⟧ {C}) (eval✓ p)
eval✓ (conginl⋙ {A} {B} p)              = cong (⟦ι₁⟧ {A} {B}) (eval✓ p)
eval✓ (conginr⋙ {A} {B} p)              = cong (⟦ι₂⟧ {A} {B}) (eval✓ p)
eval✓ (congcase⋙ {A} {B} {C} p q r)     = cong³ (⟦elim⊎⟧ {A} {B} {C}) (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (beta▻⋙ {A} {B} {t} {u})          = sym (oops₁ {A} {B} {_} {t} {u})
eval✓ (eta▻⋙ {A} {B} {t})               = oops₂ {A} {B} {_} {t}
eval✓ beta∧₁⋙                           = refl
eval✓ beta∧₂⋙                           = refl
eval✓ eta∧⋙                             = refl
eval✓ eta⊤⋙                            = refl
eval✓ (beta∨₁⋙ {A} {B} {C} {t} {u} {v}) = sym (oops₃ {A} {B} {C} {_} {t} {u} {v})
eval✓ (beta∨₂⋙ {A} {B} {C} {t} {u} {v}) = sym (oops₄ {A} {B} {C} {_} {t} {u} {v})
eval✓ (eta∨⋙ {A} {B} {t})               = oops₅ {A} {B} {_} {t}
