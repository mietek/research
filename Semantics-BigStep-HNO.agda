---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-HNO where

open import Semantics-BigStep
open HNO public
import Semantics-BigStep-HS as BS-HS


---------------------------------------------------------------------------------------------------------------

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                = var
na←naxnf-⇓ (app p₁) (applam r₁ r)      = case (BS-HS.na←naxnf-⇓ p₁ r₁) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁ r₁′ r₂) = app

na←hnf-⇓ : ∀ {n} {e : Tm n} {e′} → HNF e → NA e → e ⇓ e′ → NA e′
na←hnf-⇓ (lam p) () r
na←hnf-⇓ (hnf p) q  r = na←naxnf-⇓ p r

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r)            = lam (nf-⇓ r)
nf-⇓ (applam r₁ r)      = nf-⇓ r
nf-⇓ (app r₁ q₁ r₁′ r₂) = nf (app (nanf←nf (nf-⇓ r₁′) (na←hnf-⇓ (BS-HS.hnf-⇓ r₁) q₁ r₁′)) (nf-⇓ r₂))

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (BS-HS.refl-⇓′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------

-- TODO
--   ss↔bsx : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS.HNO.⇒* e′ ↔ e BSX.HNO.⇓ e′
--   ss↔bsx = BSX.HNO.ss↔bsx


---------------------------------------------------------------------------------------------------------------
