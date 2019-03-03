---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBV where

open import Semantics-BigStep
open CBV public
import Semantics-SmallStep-CBV as SS-CBV


---------------------------------------------------------------------------------------------------------------

wnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WNF e′
wnf-⇓ var              = wnf var
wnf-⇓ lam              = lam
wnf-⇓ (applam r₁ r₂ r) = wnf-⇓ r
wnf-⇓ (app r₁ q₁ r₂)   = wnf (app (nawnf←wnf (wnf-⇓ r₁) q₁) (wnf-⇓ r₂))

na←nawnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇓ e′ → NA e′
na←nawnf-⇓ var         var              = var
na←nawnf-⇓ (app p₁ p₂) (applam r₁ r₂ r) = case (nawnf←wnf (wnf-⇓ r₁) (na←nawnf-⇓ p₁ r₁)) of λ ()
na←nawnf-⇓ (app p₁ p₂) (app r₁ q₁ r₂ )  = app

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → WNF e → e ⇓ e
  refl-⇓ lam     = lam
  refl-⇓ (wnf p) = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NAWNF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nawnf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e SS-CBV.⇒* e′
ss←bs var              = ε
ss←bs lam              = ε
ss←bs (applam r₁ r₂ r) = SS-CBV.bs-applam (ss←bs r₁) (ss←bs r₂) (wnf-⇓ r₂) (ss←bs r)
ss←bs (app r₁ q₁′ r₂)  = SS-CBV.bs-app (ss←bs r₁) (wnf-⇓ r₁) (ss←bs r₂)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e SS-CBV.⇒*⟨ i ⟩ e′ → WNF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e SS-CBV.⇒ e′ → e′ SS-CBV.⇒*⟨ i ⟩ e″ → WNF e″ → e ⇓ e″
  bs←ss′ (SS-CBV.app₁ r₁)    rs p″             with SS-CBV.rev-app-⇒* rs p″
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss′ r₁ rs₁ lam)
                                                         (bs←ss rs₂ p₂′)
                                                         (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss′ r₁ rs₁ (wnf p₁′))
                                                      (na←nawnf p₁′)
                                                      (bs←ss rs₂ p₂′)
  bs←ss′ (SS-CBV.app₂ p₁ r₂) rs p″             with SS-CBV.rev-app-⇒* rs p″
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss rs₁ lam)
                                                         (bs←ss′ r₂ rs₂ p₂′)
                                                         (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss rs₁ (wnf p₁′))
                                                      (na←nawnf p₁′)
                                                      (bs←ss′ r₂ rs₂ p₂′)
  bs←ss′ (SS-CBV.applam p₂)  rs p″             = applam lam (refl-⇓ p₂) (bs←ss rs p″)

ss↔bs : ∀ {n} {e : Tm n} {e′} → WNF e′ → e SS-CBV.⇒* e′ ↔ e ⇓ e′
ss↔bs p′ = (λ r → bs←ss r p′) , ss←bs


---------------------------------------------------------------------------------------------------------------
