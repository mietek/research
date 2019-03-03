---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBN where

open import Semantics-BigStep
open CBN public
import Semantics-SmallStep-CBN as SS-CBN


---------------------------------------------------------------------------------------------------------------

whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e′
whnf-⇓ var           = whnf var
whnf-⇓ lam           = lam
whnf-⇓ (applam r₁ r) = whnf-⇓ r
whnf-⇓ (app r₁ q₁)   = whnf (app (naxnf←whnf (whnf-⇓ r₁) q₁))

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var           = var
na←naxnf-⇓ (app p₁) (applam r₁ r) = case (naxnf←whnf (whnf-⇓ r₁) (na←naxnf-⇓ p₁ r₁)) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁)   = app

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → WHNF e → e ⇓ e
refl-⇓ lam      = lam
refl-⇓ (whnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-CBN.⇒* e′
ss←bs var           = ε
ss←bs lam           = ε
ss←bs (applam r₁ r) = SS-CBN.bs-applam (ss←bs r₁) (ss←bs r)
ss←bs (app r₁ q₁)   = SS-CBN.bs-app (ss←bs r₁)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-CBN.⇒*⟨ i ⟩ e′ → WHNF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-CBN.⇒ e′ → e′ SS-CBN.⇒*⟨ i ⟩ e″ → WHNF e″ → e ⇓ e″
  bs←ss′ SS-CBN.applam    rs p″    = applam lam (bs←ss rs p″)
  bs←ss′ (SS-CBN.app₁ r₁) rs p″    with SS-CBN.rev-app-⇒* rs p″
  ... | inj₁ (_ , rs′ , rs″)        = applam (bs←ss′ r₁ rs′ lam) (bs←ss rs″ p″)
  ... | inj₂ (_ , rs′ , p₁′ , refl) = app (bs←ss′ r₁ rs′ (whnf p₁′)) (na←naxnf p₁′)

ss↔bs : ∀ {n e′} {e : Tm n} → WHNF e′ → e SS-CBN.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
