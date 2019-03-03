---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-HAO where

open import Semantics-BigStep
open HAO public
import Semantics-BigStep-CBV as BS-CBV


---------------------------------------------------------------------------------------------------------------

na←nawnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇓ e′ → NA e′
na←nawnf-⇓ var         var                = var
na←nawnf-⇓ (app p₁ p₂) (applam r₁ r₂ r)   = case (BS-CBV.na←nawnf-⇓ p₁ r₁) of λ ()
na←nawnf-⇓ (app p₁ p₂) (app r₁ q₁ r₁′ r₂) = app

na←wnf-⇓ : ∀ {n} {e : Tm n} {e′} → WNF e → NA e → e ⇓ e′ → NA e′
na←wnf-⇓ lam     () r
na←wnf-⇓ (wnf p) q  r = na←nawnf-⇓ p r

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r)            = lam (nf-⇓ r)
nf-⇓ (applam r₁ r₂ r)   = nf-⇓ r
nf-⇓ (app r₁ q₁ r₁′ r₂) = nf (app (nanf←nf (nf-⇓ r₁′) (na←wnf-⇓ (BS-CBV.wnf-⇓ r₁) q₁ r₁′)) (nf-⇓ r₂))

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (BS-CBV.refl-⇓′ (nawnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------

-- TODO
--   ss↔bsx : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS.HAO.⇒* e′ ↔ e BSX.HAO.⇓ e′
--   ss↔bsx = BSX.HAO.ss↔bsx


---------------------------------------------------------------------------------------------------------------
