---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-NO₁ where

open import Semantics-BigStep
open NO public
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-SmallStep-NO₂ as SS-NO₂
open import Semantics-SmallStep-NO₁
import Semantics-BigStep-CBN as BS-CBN
import Semantics-BigStep-NO₂ as BS-NO₂


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO goes to NF

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                = var
na←naxnf-⇓ (app p₁) (applam r₁ r)      = case (BS-CBN.na←naxnf-⇓ p₁ r₁) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁ r₁′ r₂) = app

na←whnf-⇓ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⇓ e′ → NA e′
na←whnf-⇓ lam      () r
na←whnf-⇓ (whnf p) q  r = na←naxnf-⇓ p r

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r)            = lam (nf-⇓ r)
nf-⇓ (applam r₁ r)      = nf-⇓ r
nf-⇓ (app r₁ q₁ r₁′ r₂) = nf (app (nanf←nf (nf-⇓ r₁′) p₁) (nf-⇓ r₂))
  where
    p₁ = na←whnf-⇓ (BS-CBN.whnf-⇓ r₁) q₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (BS-CBN.refl-⇓′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO implies SS-NO

bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
bs-lam = lam*

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} →
            e₁ SS-CBN.⇒* lam e₁′ → e₁′ [ e₂ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ rs = cbn-app₁* rs₁ ◅◅ applam* ◅◅ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
         e₁ SS-CBN.⇒* e₁′ → NAXNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ →
         app e₁ e₂ ⇒* app e₁″ e₂′
bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ = cbn-app₁* rs₁ ◅◅ app₁₊* p₁′ rs₁′ ◅◅ app₂* p₁″ rs₂

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var                = ε
ss←bs (lam r)            = bs-lam (ss←bs r)
ss←bs (applam r₁ r)      = bs-applam (BS-CBN.ss←bs r₁) (ss←bs r)
ss←bs (app r₁ q₁ r₁′ r₂) = bs-app (BS-CBN.ss←bs r₁) p₁ (ss←bs r₁′) p₁′ (ss←bs r₂)
  where
    p₁  = naxnf←whnf (BS-CBN.whnf-⇓ r₁) q₁
    p₁′ = nanf←nf (nf-⇓ r₁′) (na←whnf-⇓ (BS-CBN.whnf-⇓ r₁) q₁ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO to NF implies BS-NO

no←cbn|no₂-⇓ : ∀ {n} {e : Tm n} {e′ e″} → e CBN.⇓ e′ → e′ NO₂.⇓ e″ → e ⇓ e″
no←cbn|no₂-⇓ CBN.var           NO₂.var                  = var
no←cbn|no₂-⇓ CBN.lam           (NO₂.lam r r′)           = lam (no←cbn|no₂-⇓ r r′)
no←cbn|no₂-⇓ (CBN.applam r₁ r) r′                       = applam r₁ (no←cbn|no₂-⇓ r r′)
no←cbn|no₂-⇓ (CBN.app r₁ q₁)   (NO₂.app q₁′ r₁′ r₂ r₂′) = app r₁ q₁ r₁″ (no←cbn|no₂-⇓ r₂ r₂′)
  where
    r₁″ = no←cbn|no₂-⇓ (BS-CBN.refl-⇓ (BS-CBN.whnf-⇓ r₁)) r₁′

bs←ss : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ → e ⇓ e′
bs←ss rs p′             with cbn|no₂←no₁-⇒* rs p′
... | _ , rs′ , p″ , rs″ = no←cbn|no₂-⇓ (BS-CBN.bs←ss rs′ p″) (BS-NO₂.bs←ss rs″ p′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO and SS-NO to NF coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × NF e′)
bs↔ss = (λ r → ss←bs r , nf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
