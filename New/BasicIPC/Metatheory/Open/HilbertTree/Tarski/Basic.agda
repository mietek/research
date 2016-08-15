module New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.Basic where

open import New.BasicIPC.Syntax.Open.HilbertTree public
open import New.BasicIPC.Semantics.Tarski.Basic public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = (eval t γ) (eval u γ)
eval ci        γ = id
eval ck        γ = const
eval cs        γ = ap
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval tt        γ = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
check refl⇒                      = refl
check (trans⇒ p q)               = trans (check p) (check q)
check (sym⇒ p)                   = sym (check p)
check (congapp⇒ {A} {B} p q)     = cong₂ (_$ˢᶜ_ {A} {B}) (check p) (check q)
check (congi⇒ p)                 = cong id (check p)
check (congk⇒ p q)               = cong₂ const (check p) (check q)
check (congs⇒ {A} {B} {C} p q r) = cong₃ (apˢᶜ {A} {B} {C}) (check p) (check q) (check r)
check (congpair⇒ {A} {B} p q)    = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
check (congfst⇒ {A} {B} p)       = cong (π₁ˢᶜ {A} {B}) (check p)
check (congsnd⇒ {A} {B} p)       = cong (π₂ˢᶜ {A} {B}) (check p)
check beta▻ₖ⇒                    = refl
check beta▻ₛ⇒                    = refl
check beta∧₁⇒                    = refl
check beta∧₂⇒                    = refl
check eta∧⇒                      = refl
check eta⊤⇒                     = refl
