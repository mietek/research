---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-HNO where

open import Semantics-BigStep
open HNO public
import Semantics-BigStep-HS as BS-HS


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO goes to NF

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


---------------------------------------------------------------------------------------------------------------
--
-- BS-HNO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (BS-HS.refl-⇓′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- TODO: BS-HNO implies SS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- TODO: SS-HNO to NF implies BS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- TODO: BS-HNO and SS-HNO to NF coincide

-- bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × NF e′)
-- bs↔ss = (λ r → ss←bs r , nf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
