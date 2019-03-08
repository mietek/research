---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-HAO

module 3-5-Properties-BigStep-HAO where

open import 1-4-Semantics-BigStep
open HAO public
import 3-3-Properties-BigStep-CBV as BS-CBV


---------------------------------------------------------------------------------------------------------------
--
-- BS-HAO goes to NF

na←nawnf-cbv-⇓ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e CBV.⇓ e′ → NA e′
na←nawnf-cbv-⇓ var         CBV.var              = var
na←nawnf-cbv-⇓ (app p₁ p₂) (CBV.applam r₁ r₂ r) = case p₁′ of λ ()
  where
    p₁′ = nawnf←wnf (BS-CBV.wnf-⇓ r₁) (na←nawnf-cbv-⇓ p₁ r₁)
na←nawnf-cbv-⇓ (app p₁ p₂) (CBV.app r₁ p₁′ r₂)  = app

na←nawnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇓ e′ → NA e′
na←nawnf-⇓ var         var                 = var
na←nawnf-⇓ (app p₁ p₂) (applam r₁ r₂ r)    = case (na←nawnf-cbv-⇓ p₁ r₁) of λ ()
na←nawnf-⇓ (app p₁ p₂) (app r₁ p₁′ r₁′ r₂) = app

na←wnf-⇓ : ∀ {n} {e : Tm n} {e′} → WNF e → NA e → e ⇓ e′ → NA e′
na←wnf-⇓ lam     () r
na←wnf-⇓ (wnf p) p′ r = na←nawnf-⇓ p r

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                 = nf var
nf-⇓ (lam r)             = lam (nf-⇓ r)
nf-⇓ (applam r₁ r₂ r)    = nf-⇓ r
nf-⇓ (app r₁ p₁′ r₁′ r₂) = nf (app p₁ (nf-⇓ r₂))
  where
    p₁ = nanf←nf (nf-⇓ r₁′) (na←wnf-⇓ (BS-CBV.wnf-⇓ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-HAO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (BS-CBV.refl-⇓′ (nawnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
