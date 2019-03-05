---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-AO where

open import Semantics-BigStep
open AO public
open import Semantics-SmallStep-AO


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO goes to NF

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var              = nf var
nf-⇓ (lam r)          = lam (nf-⇓ r)
nf-⇓ (applam r₁ r₂ r) = nf-⇓ r
nf-⇓ (app r₁ q r₂)    = nf (app (nanf←nf (nf-⇓ r₁) q) (nf-⇓ r₂))


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ (var)       = var
  refl-⇓′ (app p₁ p₂) = app (refl-⇓′ p₁) (na←nanf p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO implies SS-AO

bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
bs-lam = lam*

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → NF (lam e₁′) → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ (lam p₁′) rs₂ p₂′ rs = app₂* rs₂ ◅◅ app₁* rs₁ p₂′ ◅◅ applam* p₁′ p₂′ ◅◅ rs
bs-applam rs₁ (nf ())   rs₂ p₂′ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
         e₁ ⇒* e₁′ → e₂ ⇒* e₂′ → NF e₂′ →
         app e₁ e₂ ⇒* app e₁′ e₂′
bs-app rs₁ rs₂ p₂′ = app₂* rs₂ ◅◅ app₁* rs₁ p₂′

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var              = ε
ss←bs (lam r)          = bs-lam (ss←bs r)
ss←bs (applam r₁ r₂ r) = bs-applam (ss←bs r₁) (nf-⇓ r₁) (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
ss←bs (app r₁ p₁′ r₂)  = bs-app (ss←bs r₁) (ss←bs r₂) (nf-⇓ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO to NF implies BS-AO

rev-lam-⇒* : ∀ {n i} {e : Tm (suc n)} {e′} → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
rev-lam-⇒* ε            = ε
rev-lam-⇒* (lam r ◅ rs) = r ◅ rev-lam-⇒* rs

¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

rev-app₁-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               NF e₂ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × NF e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × app e₁′ e₂ ≡ e′)
rev-app₁-⇒* p₂ ε                    (nf (app p₁ p₂′)) = inj₂ (_ , ε , p₁ , refl)
rev-app₁-⇒* p₂ (applam p₁ p₂′ ◅ rs) p′                = inj₁ (_ , ε , p₁ , rs)
rev-app₁-⇒* p₂ (app₁ r₁ p₂′ ◅ rs)   p′                with rev-app₁-⇒* p₂ rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs′)                       = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)                      = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)
rev-app₁-⇒* p₂ (app₂ r₂ ◅ rs)       p′                = (_ , r₂) ↯ nrf←nf p₂

rev-app₂-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
               (∃² λ e₁′ e₂′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ ×
                 e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃² λ e₁′ e₂′ → e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ ×
                 app e₁′ e₂′ ≡ e′)
rev-app₂-⇒* ε                   (nf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
rev-app₂-⇒* (applam p₁ p₂ ◅ rs) p′               = inj₁ (_ , ε , p₁ , ε , p₂ , rs)
rev-app₂-⇒* (app₁ r₁ p₂ ◅ rs)   p′               with rev-app₁-⇒* p₂ rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs′)                  = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , ε , p₂ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)                 = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , ε , p₂ , refl)
rev-app₂-⇒* (app₂ r₂ ◅ rs)      p′               with rev-app₂-⇒* rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)      = inj₁ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)     = inj₂ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , refl)

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
  bs←ss′ (lam r)        rs (lam p″)            = lam (bs←ss′ r (rev-lam-⇒* rs ) p″)
  bs←ss′ (lam r)        rs (nf var)            = rs ↯ ¬lam⇒*var
  bs←ss′ (lam r)        rs (nf (app _ _))      = rs ↯ ¬lam⇒*app
  bs←ss′ (applam p₁ p₂) rs p″                  = applam (refl-⇓ (lam p₁)) (refl-⇓ p₂) (bs←ss rs p″)
  bs←ss′ (app₁ r₁ p₂)   rs p″                  with rev-app₁-⇒* p₂ rs p″
  ... | inj₁ (_ , rs₁ , p₁′ , rs′)              = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (refl-⇓ p₂) (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , refl)             = app (bs←ss′ r₁ rs₁ (nf p₁′)) (na←nanf p₁′) (refl-⇓ p₂)
  bs←ss′ (app₂ r₂)      rs p″                  with rev-app₂-⇒* rs p″
  ... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)  = applam (bs←ss rs₁ (lam p₁′)) (bs←ss′ r₂ rs₂ p₂′) (bs←ss rs′ p″)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss rs₁ (nf p₁′)) (na←nanf p₁′) (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- BS-AO and SS-AO to NF coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × NF e′)
bs↔ss = (λ r → ss←bs r , nf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
