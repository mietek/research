---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-NO₊ where

open import Semantics-BigStep
open NO₊ public
import Semantics-SmallStep-NO₊ as SS-NO₊
import Semantics-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                = var
na←naxnf-⇓ (app p₁) (app q₁ r₁ r₂ r₂′) = app

na←whnf-⇓ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⇓ e′ → NA e′
na←whnf-⇓ lam      () r
na←whnf-⇓ (whnf p) q  r = na←naxnf-⇓ p r

rev-whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e
rev-whnf-⇓ var                = whnf var
rev-whnf-⇓ (lam r r′)         = lam
rev-whnf-⇓ (app q₁ r₁ r₂ r₂′) = whnf (app (naxnf←whnf (rev-whnf-⇓ r₁) q₁))

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r r′)         = lam (nf-⇓ r′)
nf-⇓ (app q₁ r₁ r₂ r₂′) = nf (app (nanf←nf (nf-⇓ r₁) (na←whnf-⇓ (rev-whnf-⇓ r₁) q₁ r₁)) (nf-⇓ r₂′))

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (BS-CBN.refl-⇓ (whnf←nf p)) (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (na←nanf p₁) (refl-⇓ (nf p₁)) (BS-CBN.refl-⇓ (whnf←nf p₂)) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-NO₊.⇒* e′
ss←bs var                = ε
ss←bs (lam r r′)         = SS-NO₊.bs-lam (BS-CBN.ss←bs r) (ss←bs r′)
ss←bs (app q₁ r₁ r₂ r₂′) = SS-NO₊.bs-app p₁ (ss←bs r₁) p₁′ (BS-CBN.ss←bs r₂) (ss←bs r₂′)
  where
    p₁  = naxnf←whnf (rev-whnf-⇓ r₁) q₁
    p₁′ = nanf←nf (nf-⇓ r₁) (na←whnf-⇓ (rev-whnf-⇓ r₁) q₁ r₁)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-NO₊.⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-NO₊.⇒ e′ → e′ SS-NO₊.⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
  bs←ss′ (SS-NO₊.app₁₊ p₁ r₁)     rs p″             with SS-NO₊.rev-app₁₊-⇒* rs p″
  ... | _ , rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl = app (na←naxnf p₁) (bs←ss′ r₁ rs₁ (nf p₁′))
                                                           (BS-CBN.bs←ss rs₂ p₂) (bs←ss rs₂′ p₂′)
  bs←ss′ (SS-NO₊.app₂₋ p₁ ¬p₂ r₂) rs p″             with SS-NO₊.rev-app₂₋-⇒* p₁ rs p″
  ... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl             = app (na←nanf p₁) (refl-⇓ (nf p₁))
                                                           (BS-CBN.bs←ss′ r₂ rs₂ p₂) (bs←ss rs₂′ p₂′)
  bs←ss′ (SS-NO₊.app₂₊ p₁ p₂ r₂)  rs p″             with SS-NO₊.rev-app₂₊-⇒* p₁ (SS-NO₊.whnf-⇒ r₂) rs p″
  ... | _ , rs₂ , p₂′ , refl                         = app (na←nanf p₁) (refl-⇓ (nf p₁))
                                                           (BS-CBN.refl-⇓ p₂) (bs←ss′ r₂ rs₂ p₂′)
  bs←ss′ (SS-NO₊.lam₋ ¬p r)       rs (lam p″)       with SS-NO₊.rev-lam₋-⇒* rs p″
  ... | _ , rs′ , p′ , rs″                           = lam (BS-CBN.bs←ss′ r rs′ p′) (bs←ss rs″ p″)
  bs←ss′ (SS-NO₊.lam₋ ¬p r)       rs (nf var)       = rs ↯ SS-NO₊.¬lam⇒*var
  bs←ss′ (SS-NO₊.lam₋ ¬p r)       rs (nf (app _ _)) = rs ↯ SS-NO₊.¬lam⇒*app
  bs←ss′ (SS-NO₊.lam₊ p r)        rs (lam p″)       with SS-NO₊.rev-lam₊-⇒* (SS-NO₊.whnf-⇒ r) rs
  ... | rs′                                          = lam (BS-CBN.refl-⇓ p) (bs←ss′ r rs′ p″)
  bs←ss′ (SS-NO₊.lam₊ p r)        rs (nf var)       = rs ↯ SS-NO₊.¬lam⇒*var
  bs←ss′ (SS-NO₊.lam₊ p r)        rs (nf (app _ _)) = rs ↯ SS-NO₊.¬lam⇒*app


---------------------------------------------------------------------------------------------------------------
