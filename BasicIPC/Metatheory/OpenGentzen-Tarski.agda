module BasicIPC.Metatheory.OpenGentzen-Tarski where

open import BasicIPC.Syntax.OpenGentzen public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (γ , a)
eval (app t u)  γ = eval t γ $ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙

-- Alternative version.
eval′ : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval′ (var i)            γ = lookup i γ
eval′ (lam {A} {B} t)    γ = ⟦λ⟧ {A} {B} (eval′ t) γ
eval′ (app {A} {B} t u)  γ = _⟦$⟧_ {A} {B} (eval′ t) (eval′ u) γ
eval′ (pair {A} {B} t u) γ = _⟦,⟧_ {A} {B} (eval′ t) (eval′ u) γ
eval′ (fst {A} {B} t)    γ = ⟦π₁⟧ {A} {B} (eval′ t) γ
eval′ (snd {A} {B} t)    γ = ⟦π₂⟧ {A} {B} (eval′ t) γ
eval′ tt                 γ = ∙


-- Correctness of evaluation with respect to conversion.

-- FIXME: How to show this?
postulate
  oops₁ : ∀ {{_ : Model}} {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
          → eval ([ top ≔ u ] t) ≡ (λ γ → eval t (γ , eval u γ))
  oops₂ : ∀ {{_ : Model}} {A B Γ} {t : Γ ⊢ A ▻ B}
          → eval t ≡ (λ γ a → eval (mono⊢ (weak⊆ {A = A}) t) (γ , a) a)

check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
check refl⇒                    = refl
check (trans⇒ p q)             = trans (check p) (check q)
check (sym⇒ p)                 = sym (check p)
check (conglam⇒ {A} {B} p)     = cong (⟦λ⟧ {A} {B}) (check p)
check (congapp⇒ {A} {B} p q)   = cong₂ (_⟦$⟧_ {A} {B}) (check p) (check q)
check (congpair⇒ {A} {B} p q)  = cong₂ (_⟦,⟧_ {A} {B}) (check p) (check q)
check (congfst⇒ {A} {B} p)     = cong (⟦π₁⟧ {A} {B}) (check p)
check (congsnd⇒ {A} {B} p)     = cong (⟦π₂⟧ {A} {B}) (check p)
check (beta▻⇒ {A} {B} {t} {u}) = sym (oops₁ {A} {B} {_} {t} {u})
check (eta▻⇒ {A} {B} {t})      = oops₂ {A} {B} {_} {t}
check beta∧₁⇒                  = refl
check beta∧₂⇒                  = refl
check eta∧⇒                    = refl
check eta⊤⇒                   = refl
