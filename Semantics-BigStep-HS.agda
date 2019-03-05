---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-HS where

open import Semantics-BigStep
open HS public
open import Semantics-SmallStep-HS


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS goes to HNF

hnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → HNF e′
hnf-⇓ var           = hnf var
hnf-⇓ (lam r)       = lam (hnf-⇓ r)
hnf-⇓ (applam r₁ r) = hnf-⇓ r
hnf-⇓ (app r₁ q₁)   = hnf (app (naxnf←hnf (hnf-⇓ r₁) q₁))


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-HNO

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var           = var
na←naxnf-⇓ (app p₁) (applam r₁ r) = case (na←naxnf-⇓ p₁ r₁) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁)   = app


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS is reflexive

refl-⇓′ : ∀ {n} {e : Tm n} → NAXNF e → e ⇓ e
refl-⇓′ var      = var
refl-⇓′ (app p₁) = app (refl-⇓′ p₁) (na←naxnf p₁)

refl-⇓ : ∀ {n} {e : Tm n} → HNF e → e ⇓ e
refl-⇓ (lam p) = lam (refl-⇓ p)
refl-⇓ (hnf p) = refl-⇓′ p


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS implies SS-HS

bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
bs-lam = lam*

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} →
            e₁ ⇒* lam e₁′ → HNF (lam e₁′) → e₁′ [ e₂ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ (lam p₁′) rs = app₁* rs₁ ◅◅ applam* p₁′ ◅◅ rs
bs-applam rs₁ (hnf ())  rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
bs-app = app₁*

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var           = ε
ss←bs (lam r)       = bs-lam (ss←bs r)
ss←bs (applam r₁ r) = bs-applam (ss←bs r₁) (hnf-⇓ r₁) (ss←bs r)
ss←bs (app r₁ p₁′)  = bs-app (ss←bs r₁)


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS to HNF implies BS-HS

rev-lam-⇒* : ∀ {n i} {e : Tm (suc n)} {e′} → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
rev-lam-⇒* ε            = ε
rev-lam-⇒* (lam r ◅ rs) = r ◅ rev-lam-⇒* rs

¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

rev-app₁-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → HNF e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × HNF e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ e₁′ × NAXNF e₁′ × app e₁′ e₂ ≡ e′)
rev-app₁-⇒* ε                (hnf (app p₁)) = inj₂ (_ , ε , p₁ , refl)
rev-app₁-⇒* (applam p₁ ◅ rs) p′             = inj₁ (_ , ε , p₁ , rs)
rev-app₁-⇒* (app₁ r₁ ◅ rs)   p′             with rev-app₁-⇒* rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs′)             = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)            = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → HNF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → HNF e″ → e ⇓ e″
  bs←ss′ (lam r)     rs (lam p″)      = lam (bs←ss′ r (rev-lam-⇒* rs) p″)
  bs←ss′ (lam r)     rs (hnf var)     = rs ↯ ¬lam⇒*var
  bs←ss′ (lam r)     rs (hnf (app _)) = rs ↯ ¬lam⇒*app
  bs←ss′ (applam p₁) rs p″            = applam (refl-⇓ (lam p₁)) (bs←ss rs p″)
  bs←ss′ (app₁ r₁)   rs p″            with rev-app₁-⇒* rs p″
  ... | inj₁ (_ , rs₁ , p₁′ , rs′)     = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , refl)    = app (bs←ss′ r₁ rs₁ (hnf p₁′)) (na←naxnf p₁′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-HS and SS-HS to HNF coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × HNF e′)
bs↔ss = (λ r → ss←bs r , hnf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
