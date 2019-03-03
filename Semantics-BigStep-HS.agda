---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-HS where

open import Semantics-BigStep
open HS public


---------------------------------------------------------------------------------------------------------------

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var           = var
na←naxnf-⇓ (app p₁) (applam r₁ r) = case (na←naxnf-⇓ p₁ r₁) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁)   = app

hnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → HNF e′
hnf-⇓ var           = hnf var
hnf-⇓ (lam r)       = lam (hnf-⇓ r)
hnf-⇓ (applam r₁ r) = hnf-⇓ r
hnf-⇓ (app r₁ q₁)   = hnf (app (naxnf←hnf (hnf-⇓ r₁) q₁))

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var      = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → HNF e → e ⇓ e
refl-⇓ (lam p) = lam (refl-⇓ p)
refl-⇓ (hnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------

-- TODO
--   ss↔bsx : ∀ {n} {e : Tm n} {e′} → HNF e′ → e SS.HS.⇒* e′ ↔ e BSX.HS.⇓ e′
--   ss↔bsx = BSX.HS.ss↔bsx


---------------------------------------------------------------------------------------------------------------
