---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-AO and BS-AO
--
--        SS-AO       ⎫     SS-AO
--  4.4.1 ↓ × ↑ 4.4.2 ⎬ 4.4.3 ↕
--        BS-AO       ⎭     BS-AO

module 4-4-Equivalence-AO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-4-Properties-SmallStep-AO as SS-AO
import 3-4-Properties-BigStep-AO as BS-AO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.4.1.  SS-AO to NF implies BS-AO

module Lem-4-4-1 where
  open SS-AO
  open BS-AO

  rev-lam* : ∀ {n i} {e : Tm (suc n)} {e′} → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
  rev-lam* ε            = ε
  rev-lam* (lam r ◅ rs) = r ◅ rev-lam* rs

  ¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
  ¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

  ¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

  rev-app₂* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              NF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ≡ lam e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃ λ e₂′ →
                NANF e₁ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁ e₂′ ≡ e′)
  rev-app₂* p₁ ε                    (nf (app p₁′ p₂)) = inj₂ (_ , p₁′ , ε , p₂ , refl)
  rev-app₂* p₁ (applam p₁′ p₂ ◅ rs) p′                = inj₁ (_ , refl , p₁′ , ε , p₂ , rs)
  rev-app₂* p₁ (app₁ r₁ ◅ rs)       p′                = (_ , r₁) ↯ nrf←nf p₁
  rev-app₂* p₁ (app₂ p₁′ r₂ ◅ rs)   p′                with rev-app₂* p₁′ rs p′
  ... | inj₁ (_ , refl , p₁″ , rs₂ , p₂′ , rs′)       = inj₁ (_ , refl , p₁″ , r₂ ◅ rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , p₁″ , rs₂ , p₂′ , refl)             = inj₂ (_ , p₁″ , r₂ ◅ rs₂ , p₂′ , refl)

  rev-app₁* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁′ e₂′ ≡ e′)
  rev-app₁* ε                   (nf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
  rev-app₁* (applam p₁ p₂ ◅ rs) p′               = inj₁ (_ , ε , p₁ , ε , p₂ , rs)
  rev-app₁* (app₁ r₁ ◅ rs)      p′               with rev-app₁* rs p′
  ... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)   = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)  = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂′ , refl)
  rev-app₁* (app₂ p₁ r₂ ◅ rs)   p′               with rev-app₂* p₁ rs p′
  ... | inj₁ (_ , refl , p₁′ , rs₂ , p₂′ , rs′)  = inj₁ (_ , ε , p₁′ , r₂ ◅ rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , p₁′ , rs₂ , p₂′ , refl)        = inj₂ (_ , ε , p₁′ , r₂ ◅ rs₂ , p₂′ , refl)

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
    bs←ss ε        p′ = refl-⇓ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
    bs←ss′ (lam r)        rs (lam p″)            = lam (bs←ss′ r (rev-lam* rs ) p″)
    bs←ss′ (lam r)        rs (nf var)            = rs ↯ ¬lam⇒*var
    bs←ss′ (lam r)        rs (nf (app _ _))      = rs ↯ ¬lam⇒*app
    bs←ss′ (applam p₁ p₂) rs p″                  = applam (refl-⇓ (lam p₁)) (refl-⇓ p₂) (bs←ss rs p″)
    bs←ss′ (app₁ r₁)      rs p″                  with rev-app₁* rs p″
    ... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)  = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (bs←ss rs₂ p₂′)
                                                           (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss′ r₁ rs₁ (nf p₁′)) (na←nanf p₁′)
                                                        (bs←ss rs₂ p₂′)
    bs←ss′ (app₂ p₁ r₂)   rs p″                  with rev-app₂* p₁ rs p″
    ... | inj₁ (_ , refl , p₁′ , rs₂ , p₂′ , rs′) = applam (refl-⇓ (lam p₁′)) (bs←ss′ r₂ rs₂ p₂′)
                                                           (bs←ss rs′ p″)
    ... | inj₂ (_ , p₁′ , rs₂ , p₂′ , refl)       = app (refl-⇓ (nf p₁′)) (na←nanf p₁′)
                                                        (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.4.2.  BS-AO implies SS-AO

module Lem-4-4-2 where
  open SS-AO
  open BS-AO

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₁ → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₁ p₂ = applam p₁ p₂ ◅ ε

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* = map app₁

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map (app₂ p₁)

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
              e₁ ⇒* lam e₁′ → NF (lam e₁′) → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ (lam p₁′) rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* (lam p₁′) rs₂ ◅◅ applam* p₁′ p₂′ ◅◅ rs
  bs-applam rs₁ (nf ())   rs₂ p₂′ rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
           e₁ ⇒* e₁′ → NF e₁′ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁′ e₂′
  bs-app rs₁ p₁′ rs₂ = app₁* rs₁ ◅◅ app₂* p₁′ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
  ss←bs var              = ε
  ss←bs (lam r)          = bs-lam (ss←bs r)
  ss←bs (applam r₁ r₂ r) = bs-applam (ss←bs r₁) (nf-⇓ r₁) (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
  ss←bs (app r₁ p₁′ r₂)  = bs-app (ss←bs r₁) (nf-⇓ r₁) (ss←bs r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 4.4.3.  SS-AO to NF and BS-AO coincide

module Thm-4-4-3 where
  ss-ao↔bs-ao : ∀ {n} {e : Tm n} {e′} → (e SS.AO.⇒* e′ × NF e′) ↔ e BS.AO.⇓ e′
  ss-ao↔bs-ao = uncurry Lem-4-4-1.bs←ss , λ r → Lem-4-4-2.ss←bs r , BS-AO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
