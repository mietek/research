---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-H

module 2-7-1-Properties-BigStep-H where

open import 1-3-Semantics-BigStep
open H public
import 2-1-Properties-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-H goes to HNF

na←naxnf-cbn-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e CBN.⟱ e′ → NA e′
na←naxnf-cbn-⟱ var      CBN.var           = var
na←naxnf-cbn-⟱ (app p₁) (CBN.applam r₁ r) = case p₁′ of λ ()
  where
    p₁′ = naxnf←whnf (BS-CBN.whnf-⟱ r₁) (na←naxnf-cbn-⟱ p₁ r₁)
na←naxnf-cbn-⟱ (app p₁) (CBN.app r₁ p₁′)  = app

na←naxnf-⟱ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⟱ e′ → NA e′
na←naxnf-⟱ var      var              = var
na←naxnf-⟱ (app p₁) (applam r₁ r)    = case (na←naxnf-cbn-⟱ p₁ r₁) of λ ()
na←naxnf-⟱ (app p₁) (app r₁ p₁′ r₁′) = app

na←whnf-⟱ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⟱ e′ → NA e′
na←whnf-⟱ lam      () r
na←whnf-⟱ (whnf p) p′ r = na←naxnf-⟱ p r

hnf-⟱ : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → HNF e′
hnf-⟱ var              = hnf var
hnf-⟱ (lam r)          = lam (hnf-⟱ r)
hnf-⟱ (applam r₁ r)    = hnf-⟱ r
hnf-⟱ (app r₁ p₁′ r₁′) = hnf (app p₁″)
  where
    p₁″ = naxnf←hnf (hnf-⟱ r₁′) (na←whnf-⟱ (BS-CBN.whnf-⟱ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-H is reflexive

refl-⟱′ : ∀ {n} {e : Tm n} → NAXNF e → e ⟱ e
refl-⟱′ (var)    = var
refl-⟱′ (app p₁) = app (BS-CBN.refl-⟱′ p₁) (na←naxnf p₁) (refl-⟱′ p₁)

refl-⟱ : ∀ {n} {e : Tm n} → HNF e → e ⟱ e
refl-⟱ (lam p) = lam (refl-⟱ p)
refl-⟱ (hnf p) = refl-⟱′ p


---------------------------------------------------------------------------------------------------------------
