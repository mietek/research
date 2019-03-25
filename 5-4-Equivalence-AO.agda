---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-AO and BS-AO
--
--        SS-AO       ⎫     SS-AO
--  5.4.1 ↓   ↑ 5.4.2 ⎬ 5.4.3 ↕
--        BS-AO       ⎭     BS-AO

module 5-4-Equivalence-AO where

open import 1-2-Syntax-Predicates
import 2-1-Semantics-BigStep as BS
import 2-2-Semantics-SmallStep as SS
import 3-4-Properties-BigStep-AO as BS-AO
import 4-4-Properties-SmallStep-AO as SS-AO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.4.1.  SS-AO to NF implies BS-AO

module Lem-5-4-1 where
  open SS-AO
  open BS-AO

  rev-lam* : ∀ {n i s} {e : Tm (suc n)} {e′} → lam s e ⇒*⟨ i ⟩ lam s e′ → e ⇒*⟨ i ⟩ e′
  rev-lam* ε            = ε
  rev-lam* (lam r ◅ rs) = r ◅ rev-lam* rs

  ¬lam⇒*var : ∀ {n s} {e : Tm (suc n)} {s′ x} → ¬ (lam s e ⇒* var s′ x)
  ¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

  ¬lam-s⇒*lam-s′ : ∀ {n s} {e : Tm (suc n)} {s′ e′} → s ≢ s′ → ¬ (lam s e ⇒* lam s′ e′)
  ¬lam-s⇒*lam-s′ s≢s′ = λ { ε            → refl ↯ s≢s′
                           ; (lam r ◅ rs) → rs ↯ ¬lam-s⇒*lam-s′ s≢s′ }

  ¬lam⇒*app : ∀ {n s} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam s e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

  rev-app₂* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              NF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃³ λ s e₁′ e₂′ →
                e₁ ≡ lam s e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃ λ e₂′ →
                NANF e₁ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁ e₂′ ≡ e′)
  rev-app₂* p₁ ε                    (nf (app p₁′ p₂)) = inj₂ (_ , p₁′ , ε , p₂ , refl)
  rev-app₂* p₁ (applam p₁′ p₂ ◅ rs) p′                = inj₁ (_ , refl , p₁′ , ε , p₂ , rs)
  rev-app₂* p₁ (app₁ r₁ ◅ rs)       p′                = r₁ ↯ nrf←nf p₁
  rev-app₂* p₁ (app₂ p₁′ r₂ ◅ rs)   p′                with rev-app₂* p₁′ rs p′
  ... | inj₁ (_ , refl , p₁″ , rs₂ , p₂′ , rs′)       = inj₁ (_ , refl , p₁″ , r₂ ◅ rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , p₁″ , rs₂ , p₂′ , refl)             = inj₂ (_ , p₁″ , r₂ ◅ rs₂ , p₂′ , refl)

  rev-app₁* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃³ λ s e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ lam s e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
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
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⟱ e′
    bs←ss ε        p′ = refl-⟱ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⟱ e″
    bs←ss′ (applam p₁ p₂)  rs p″                  = applam (refl-⟱ (lam p₁)) (refl-⟱ p₂) (bs←ss rs p″)
    bs←ss′ (lam {s = s} r) rs (lam {s = s′} p″)   with s ≟ s′
    ... | no s≢s′                                  = rs ↯ ¬lam-s⇒*lam-s′ s≢s′
    ... | yes refl                                 = lam (bs←ss′ r (rev-lam* rs) p″)
    bs←ss′ (lam r)         rs (nf var)            = rs ↯ ¬lam⇒*var
    bs←ss′ (lam r)         rs (nf (app _ _))      = rs ↯ ¬lam⇒*app
    bs←ss′ (app₁ r₁)       rs p″                  with rev-app₁* rs p″
    ... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)   = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (bs←ss rs₂ p₂′)
                                                            (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)  = app (bs←ss′ r₁ rs₁ (nf p₁′)) (na←nanf p₁′)
                                                         (bs←ss rs₂ p₂′)
    bs←ss′ (app₂ p₁ r₂)    rs p″                  with rev-app₂* p₁ rs p″
    ... | inj₁ (_ , refl , p₁′ , rs₂ , p₂′ , rs′)  = applam (refl-⟱ (lam p₁′)) (bs←ss′ r₂ rs₂ p₂′)
                                                            (bs←ss rs′ p″)
    ... | inj₂ (_ , p₁′ , rs₂ , p₂′ , refl)        = app (refl-⟱′ p₁′) (na←nanf p₁′)
                                                         (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.4.2.  BS-AO implies SS-AO

module Lem-5-4-2 where
  open SS-AO
  open BS-AO

  applam* : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₁ → NF e₂ → app (lam s e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₁ p₂ = applam p₁ p₂ ◅ ε

  lam* : ∀ {n s} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam s e ⇒* lam s e′
  lam* = map* lam

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* = map* app₁

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map* (app₂ p₁)

  bs-applam : ∀ {n s} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
              e₁ ⇒* lam s e₁′ → NF (lam s e₁′) → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ (lam p₁′) rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* (lam p₁′) rs₂ ◅◅ applam* p₁′ p₂′ ◅◅ rs
  bs-applam rs₁ (nf ())   rs₂ p₂′ rs

  bs-lam : ∀ {n s} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam s e ⇒* lam s e′
  bs-lam = lam*

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
           e₁ ⇒* e₁′ → NF e₁′ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁′ e₂′
  bs-app rs₁ p₁′ rs₂ = app₁* rs₁ ◅◅ app₂* p₁′ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → e ⇒* e′
  ss←bs (applam r₁ r₂ r) = bs-applam (ss←bs r₁) (nf-⟱ r₁) (ss←bs r₂) (nf-⟱ r₂) (ss←bs r)
  ss←bs var              = ε
  ss←bs (lam r)          = bs-lam (ss←bs r)
  ss←bs (app r₁ p₁′ r₂)  = bs-app (ss←bs r₁) (nf-⟱ r₁) (ss←bs r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 5.4.3.  SS-AO to NF and BS-AO coincide

module Thm-5-4-3 where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → (e SS.AO.⇒* e′ × NF e′) ↔ e BS.AO.⟱ e′
  ss↔bs = uncurry Lem-5-4-1.bs←ss , λ r → Lem-5-4-2.ss←bs r , BS-AO.nf-⟱ r


---------------------------------------------------------------------------------------------------------------
