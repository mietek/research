---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-AO where

open import Semantics-BigStep
open AO public
import Semantics-SmallStep-AO as SS-AO


---------------------------------------------------------------------------------------------------------------

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var              = nf var
nf-⇓ (lam r)          = lam (nf-⇓ r)
nf-⇓ (applam r₁ r₂ r) = nf-⇓ r
nf-⇓ (app r₁ q r₂)    = nf (app (nanf←nf (nf-⇓ r₁) q) (nf-⇓ r₂))

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nanf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-AO.⇒* e′
ss←bs var              = ε
ss←bs (lam r)          = SS-AO.bs-lam (ss←bs r)
ss←bs (applam r₁ r₂ r) = SS-AO.bs-applam (ss←bs r₁) (nf-⇓ r₁) (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
ss←bs (app r₁ p₁′ r₂)  = SS-AO.bs-app (ss←bs r₁) (ss←bs r₂) (nf-⇓ r₂)

-- TODO
--   ss↔bsx : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS.AO.⇒* e′ ↔ e BSX.AO.⇓ e′
--   ss↔bsx = BSX.AO.ss↔bsx


---------------------------------------------------------------------------------------------------------------
