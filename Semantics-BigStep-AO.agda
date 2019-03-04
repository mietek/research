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

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-AO.⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-AO.⇒ e′ → e′ SS-AO.⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
  bs←ss′ (SS-AO.lam r)        rs (lam p″)       with SS-AO.rev-lam-⇒* rs p″
  ... | rs′                                      = lam (bs←ss′ r rs′ p″)
  bs←ss′ (SS-AO.lam r)        rs (nf var)       = rs ↯ SS-AO.¬lam⇒*var
  bs←ss′ (SS-AO.lam r)        rs (nf (app _ _)) = rs ↯ SS-AO.¬lam⇒*app
  bs←ss′ (SS-AO.app₂ r₂)      rs p″             with SS-AO.rev-app₂-⇒* rs p″
  ... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)   = applam (bs←ss rs₁ (lam p₁′)) (bs←ss′ r₂ rs₂ p₂′) (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)  = app (bs←ss rs₁ (nf p₁′)) (na←nanf p₁′) (bs←ss′ r₂ rs₂ p₂′)
  bs←ss′ (SS-AO.app₁ p₂ r₁)   rs p″             with SS-AO.rev-app₁-⇒* p₂ rs p″
  ... | inj₁ (_ , rs₁ , p₁′ , rs′)               = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (refl-⇓ p₂) (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , refl)              = app (bs←ss′ r₁ rs₁ (nf p₁′)) (na←nanf p₁′) (refl-⇓ p₂)
  bs←ss′ (SS-AO.applam p₁ p₂) rs p″             = applam (refl-⇓ (lam p₁)) (refl-⇓ p₂) (bs←ss rs p″)

ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-AO.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
