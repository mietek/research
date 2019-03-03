---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-NO where

open import Semantics-BigStep
open NO public
import Semantics-SmallStep-NO as SS-NO
import Semantics-BigStep-CBN as BS-CBN
import Semantics-BigStep-NO₊ as BS-NO₊


---------------------------------------------------------------------------------------------------------------

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

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (BS-CBN.refl-⇓′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)

no←cbn|no₊-⇓ : ∀ {n} {e : Tm n} {e′ e″} → e CBN.⇓ e′ → e′ NO₊.⇓ e″ → e ⇓ e″
no←cbn|no₊-⇓ CBN.var           NO₊.var                  = var
no←cbn|no₊-⇓ CBN.lam           (NO₊.lam r r′)           = lam (no←cbn|no₊-⇓ r r′)
no←cbn|no₊-⇓ (CBN.applam r₁ r) r′                       = applam r₁ (no←cbn|no₊-⇓ r r′)
no←cbn|no₊-⇓ (CBN.app r₁ q₁)   (NO₊.app q₁′ r₁′ r₂ r₂′) = app r₁ q₁ r₁″ (no←cbn|no₊-⇓ r₂ r₂′)
  where
    r₁″ = no←cbn|no₊-⇓ (BS-CBN.refl-⇓ (BS-CBN.whnf-⇓ r₁)) r₁′


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-NO.⇒* e′
ss←bs var                = ε
ss←bs (lam r)            = SS-NO.bs-lam (ss←bs r)
ss←bs (applam r₁ r)      = SS-NO.bs-applam (BS-CBN.ss←bs r₁) (ss←bs r)
ss←bs (app r₁ q₁ r₁′ r₂) = SS-NO.bs-app (BS-CBN.ss←bs r₁) p₁ (ss←bs r₁′) p₁′ (ss←bs r₂)
  where
    p₁  = naxnf←whnf (BS-CBN.whnf-⇓ r₁) q₁
    p₁′ = nanf←nf (nf-⇓ r₁′) (na←whnf-⇓ (BS-CBN.whnf-⇓ r₁) q₁ r₁′)

bs←ss : ∀ {n} {e : Tm n} {e′} → e SS-NO.⇒* e′ → NF e′ → e ⇓ e′
bs←ss rs p′             with SS-NO.cbn|no₊←no-⇒* rs p′
... | _ , rs′ , p″ , rs″ = no←cbn|no₊-⇓ (BS-CBN.bs←ss rs′ p″) (BS-NO₊.bs←ss rs″ p′)

ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-NO.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
