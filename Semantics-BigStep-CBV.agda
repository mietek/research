---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBV where

open import Semantics-BigStep
open CBV public
open import Semantics-SmallStep-CBV


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV goes to WNF

wnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WNF e′
wnf-⇓ var              = wnf var
wnf-⇓ lam              = lam
wnf-⇓ (applam r₁ r₂ r) = wnf-⇓ r
wnf-⇓ (app r₁ q₁ r₂)   = wnf (app (nawnf←wnf (wnf-⇓ r₁) q₁) (wnf-⇓ r₂))


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-HAO

na←nawnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇓ e′ → NA e′
na←nawnf-⇓ var         var              = var
na←nawnf-⇓ (app p₁ p₂) (applam r₁ r₂ r) = case (nawnf←wnf (wnf-⇓ r₁) (na←nawnf-⇓ p₁ r₁)) of λ ()
na←nawnf-⇓ (app p₁ p₂) (app r₁ q₁ r₂ )  = app


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → WNF e → e ⇓ e
  refl-⇓ lam     = lam
  refl-⇓ (wnf p) = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NAWNF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nawnf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV implies SS-CBV

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → e₂ ⇒* e₂′ → WNF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* lam rs₂ ◅◅ applam* p₂′ ◅◅ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
         e₁ ⇒* e₁′ → WNF e₁′ → e₂ ⇒* e₂′ →
         app e₁ e₂ ⇒* app e₁′ e₂′
bs-app rs₁ p₁′ rs₂ = app₁* rs₁ ◅◅ app₂* p₁′ rs₂

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var              = ε
ss←bs lam              = ε
ss←bs (applam r₁ r₂ r) = bs-applam (ss←bs r₁) (ss←bs r₂) (wnf-⇓ r₂) (ss←bs r)
ss←bs (app r₁ q₁′ r₂)  = bs-app (ss←bs r₁) (wnf-⇓ r₁) (ss←bs r₂)


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV to WNF implies BS-CBV

rev-app-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → WNF e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NAWNF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × app e₁′ e₂′ ≡ e′)
rev-app-⇒* ε                      (wnf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
rev-app-⇒* (app₁ r₁ ◅ rs)         p′                with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)               = inj₁ (_ , r₁ ◅ rs₁ , rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂′ , refl)
rev-app-⇒* (app₂ p₁ r₂ ◅ rs)      p′                with rev-app-⇒* rs p′
... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)               = inj₁ (_ , rs₁ , r₂ ◅ rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , refl)
rev-app-⇒* (applam p₂ ◅ rs)       p′                = inj₁ (_ , ε , ε , p₂ , rs)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → WNF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → WNF e″ → e ⇓ e″
  bs←ss′ (app₁ r₁)    rs p″                    with rev-app-⇒* rs p″
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss′ r₁ rs₁ lam)
                                                         (bs←ss rs₂ p₂′)
                                                         (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss′ r₁ rs₁ (wnf p₁′))
                                                      (na←nawnf p₁′)
                                                      (bs←ss rs₂ p₂′)
  bs←ss′ (app₂ p₁ r₂) rs p″                    with rev-app-⇒* rs p″
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss rs₁ lam)
                                                         (bs←ss′ r₂ rs₂ p₂′)
                                                         (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss rs₁ (wnf p₁′))
                                                      (na←nawnf p₁′)
                                                      (bs←ss′ r₂ rs₂ p₂′)
  bs←ss′ (applam p₂)  rs p″                    = applam lam (refl-⇓ p₂) (bs←ss rs p″)


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBV and SS-CBV coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × WNF e′)
bs↔ss = (λ r → ss←bs r , wnf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
