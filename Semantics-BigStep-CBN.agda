---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-CBN where

open import Semantics-BigStep
open CBN public
open import Semantics-SmallStep-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN goes to WHNF

whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e′
whnf-⇓ var           = whnf var
whnf-⇓ lam           = lam
whnf-⇓ (applam r₁ r) = whnf-⇓ r
whnf-⇓ (app r₁ q₁)   = whnf (app (naxnf←whnf (whnf-⇓ r₁) q₁))


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-NO

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var           = var
na←naxnf-⇓ (app p₁) (applam r₁ r) = case (naxnf←whnf (whnf-⇓ r₁) (na←naxnf-⇓ p₁ r₁)) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁)   = app


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN is reflexive

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var      = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → WHNF e → e ⇓ e
refl-⇓ lam      = lam
refl-⇓ (whnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN implies SS-CBN

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} → e₁ ⇒* lam e₁′ → e₁′ [ e₂ ] ⇒* e′ → app e₁ e₂ ⇒* e′
bs-applam rs₁ rs = app₁* rs₁ ◅◅ applam* ◅◅ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
bs-app = app₁*

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var           = ε
ss←bs lam           = ε
ss←bs (applam r₁ r) = bs-applam (ss←bs r₁) (ss←bs r)
ss←bs (app r₁ q₁)   = bs-app (ss←bs r₁)


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN to WHNF implies BS-CBN

rev-app₁-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → WHNF e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ e₁′ × NAXNF e₁′ × app e₁′ e₂ ≡ e′)
rev-app₁-⇒* ε              (whnf (app p₁′)) = inj₂ (_ , ε , p₁′ , refl)
rev-app₁-⇒* (applam ◅ rs)  p′               = inj₁ (_ , ε , rs)
rev-app₁-⇒* (app₁ r₁ ◅ rs) p′               with rev-app₁-⇒* rs p′
... | inj₁ (_ , rs₁ , rs′)                   = inj₁ (_ , r₁ ◅ rs₁ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)            = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → WHNF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → WHNF e″ → e ⇓ e″
  bs←ss′ applam    rs p″           = applam lam (bs←ss rs p″)
  bs←ss′ (app₁ r₁) rs p″           with rev-app₁-⇒* rs p″
  ... | inj₁ (_ , rs′ , rs″)        = applam (bs←ss′ r₁ rs′ lam) (bs←ss rs″ p″)
  ... | inj₂ (_ , rs′ , p₁′ , refl) = app (bs←ss′ r₁ rs′ (whnf p₁′)) (na←naxnf p₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-CBN and SS-CBN to WHNF coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × WHNF e′)
bs↔ss = (λ r → ss←bs r , whnf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
