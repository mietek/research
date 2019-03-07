---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HAO and BS-HAO
--
--        SS-HAO      ⎫     SS-HAO
--  4.5.1 ↓   ↑ 4.5.2 ⎬ 4.5.3 ↕
--        BS-HAO      ⎭     BS-HAO

module 4-5-Equivalence-HAO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-3-Properties-SmallStep-CBV as SS-CBV
import 2-5-1-Properties-SmallStep-HAO as SS-HAO
import 3-3-Properties-BigStep-CBV as BS-CBV
import 3-5-Properties-BigStep-HAO as BS-HAO
import 4-3-Equivalence-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.1.  SS-HAO to NF implies BS-HAO

module Lem-4-5-1 where
  open SS-HAO
  open BS-HAO

  rev-lam* : ∀ {n i} {e : Tm (suc n)} {e′} → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
  rev-lam* ε            = ε
  rev-lam* (lam r ◅ rs) = r ◅ rev-lam* rs

  ¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
  ¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

  ¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

  rev-app₂* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              NANF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃ λ e₂′ →
                e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁ e₂′ ≡ e′)
  rev-app₂* p₁ ε                  (nf (app p₁′ p₂)) = _ , ε , p₂ , refl
  rev-app₂* () (applam p₂ ◅ rs)   p′
  rev-app₂* p₁ (cbv-app₁ r₁ ◅ rs) p′                = (_ , r₁) ↯ SS-CBV.nrf←nawnf (nawnf←nanf p₁)
  rev-app₂* p₁ (app₁ p₁′ r₁ ◅ rs) p′                = (_ , r₁) ↯ nrf←nanf p₁
  rev-app₂* () (app₂ₐ r₂ ◅ rs)    p′
  rev-app₂* p₁ (app₂ p₁′ r₂ ◅ rs) p′                with rev-app₂* p₁′ rs p′
  ... | _ , rs₂ , p₂′ , refl                        = _ , r₂ ◅ rs₂ , p₂′ , refl

  rev-app₁* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              NAWNF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃² λ e₁′ e₂′ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁′ e₂′ ≡ e′)
  rev-app₁* p₁ ε                  (nf (app p₁′ p₂′)) = _ , ε , p₁′ , ε , p₂′ , refl
  rev-app₁* () (applam p₂ ◅ rs)   p′
  rev-app₁* p₁ (cbv-app₁ r₁ ◅ rs) p′                 = (_ , r₁) ↯ SS-CBV.nrf←nawnf p₁
  rev-app₁* p₁ (app₁ p₁′ r₁ ◅ rs) p′                 with rev-app₁* (nawnf-⇒ p₁′ r₁) rs p′
  ... | _ , rs₁ , p₁″ , rs₂ , p₂′ , refl             = _ , r₁ ◅ rs₁ , p₁″ , rs₂ , p₂′ , refl
  rev-app₁* () (app₂ₐ r₂ ◅ rs)    p′
  rev-app₁* p₁ (app₂ p₁′ r₂ ◅ rs) p′                 with rev-app₂* p₁′ rs p′
  ... | _ , rs₂ , p₂′ , refl                         = _ , ε , p₁′ , r₂ ◅ rs₂ , p₂′ , refl

  rev-app* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
             app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
             (∃² λ e₁′ e₂′ →
               e₁ SS.CBV.⇒*⟨ i ⟩ lam e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
             (∃³ λ e₁′ e₁″ e₂′ →
               e₁ SS.CBV.⇒*⟨ i ⟩ e₁′ × NAWNF e₁′ × e₁′ ⇒*⟨ i ⟩ e₁″ × NANF e₁″ ×
               e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁″ e₂′ ≡ e′)
  rev-app* ε                  (nf (app p₁ p₂)) = inj₂ (_ , ε , nawnf←nanf p₁ , ε , p₁ , ε , p₂ , refl)
  rev-app* (applam p₂ ◅ rs)   p′               = inj₁ (_ , ε , ε , p₂ , rs)
  rev-app* (cbv-app₁ r₁ ◅ rs) p′               with rev-app* rs p′
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)
      = inj₁ (_ , r₁ ◅ rs₁ , rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₁′ , p₁″ , rs₂ , p₂′ , refl)
      = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , rs₁′ , p₁″ , rs₂ , p₂′ , refl)
  rev-app* (app₁ p₁ r₁ ◅ rs)  p′               with rev-app₁* (nawnf-⇒ p₁ r₁) rs p′
  ... | _ , rs₁ , p₁″ , rs₂ , p₂′ , refl
      = inj₂ (_ , ε , p₁ , r₁ ◅ rs₁ , p₁″ , rs₂ , p₂′ , refl)
  rev-app* (app₂ₐ r₂ ◅ rs)    p′               with rev-app* rs p′
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)
      = inj₁ (_ , rs₁ , r₂ ◅ rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₁′ , p₁″ , rs₂ , p₂′ , refl)
      = inj₂ (_ , rs₁ , p₁′ , rs₁′ , p₁″ , r₂ ◅ rs₂ , p₂′ , refl)
  rev-app* (app₂ p₁ r₂ ◅ rs)  p′               with rev-app₂* p₁ rs p′
  ... | _ , rs₂ , p₂′ , refl
      = inj₂ (_ , ε , nawnf←nanf p₁ , ε , p₁ , r₂ ◅ rs₂ , p₂′ , refl)

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
    bs←ss ε        p′ = refl-⇓ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
    bs←ss′ (lam r)       rs (lam p″)                          = lam (bs←ss′ r (rev-lam* rs) p″)
    bs←ss′ (lam r)       rs (nf var)                          = rs ↯ ¬lam⇒*var
    bs←ss′ (lam r)       rs (nf (app _ _))                    = rs ↯ ¬lam⇒*app
    bs←ss′ (applam p₂)   rs p″                                = applam (BS-CBV.refl-⇓ lam)
                                                                        (refl-⇓ p₂)
                                                                        (bs←ss rs p″)
    bs←ss′ (cbv-app₁ r₁) rs p″                                with rev-app* rs p″
    ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)                     = applam (CBV.Lem-4-3-1.bs←ss′ r₁ rs₁ lam)
                                                                        (bs←ss rs₂ p₂′)
                                                                        (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₁′ , p₁″ , rs₂ , p₂′ , refl) = app (CBV.Lem-4-3-1.bs←ss′ r₁ rs₁ (wnf p₁′))
                                                                     (na←nawnf p₁′)
                                                                     (bs←ss rs₁′ (nf p₁″))
                                                                     (bs←ss rs₂ p₂′)
    bs←ss′ (app₁ p₁ r₁)  rs p″                                with rev-app₁* (nawnf-⇒ p₁ r₁) rs p″
    ... | _ , rs₁ , p₁′ , rs₂ , p₂′ , refl                     = app (BS-CBV.refl-⇓′ p₁)
                                                                     (na←nawnf p₁)
                                                                     (bs←ss′ r₁ rs₁ (nf p₁′))
                                                                     (bs←ss rs₂ p₂′)
    bs←ss′ (app₂ₐ r₂)    rs p″                                with rev-app* rs p″
    ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)                     = applam (CBV.Lem-4-3-1.bs←ss rs₁ lam)
                                                                        (bs←ss′ r₂ rs₂ p₂′)
                                                                        (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₁′ , p₁″ , rs₂ , p₂′ , refl) = app (CBV.Lem-4-3-1.bs←ss rs₁ (wnf p₁′))
                                                                     (na←nawnf p₁′)
                                                                     (bs←ss rs₁′ (nf p₁″))
                                                                     (bs←ss′ r₂ rs₂ p₂′)
    bs←ss′ (app₂ p₁ r₂)  rs p″                                with rev-app₂* p₁ rs p″
    ... | _ , rs₂ , p₂′ , refl                                 = app (BS-CBV.refl-⇓′ (nawnf←nanf p₁))
                                                                     (na←nanf p₁)
                                                                     (refl-⇓′ p₁)
                                                                     (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.2.  BS-HAO implies SS-HAO

module Lem-4-5-2 where
  open SS-HAO
  open BS-HAO

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₂ = applam p₂ ◅ ε

  cbv-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBV.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  cbv-app₁* = map cbv-app₁

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAWNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* p₁ ε          = ε
  app₁* p₁ (r₁ ◅ rs₁) = app₁ p₁ r₁ ◅ app₁* (nawnf-⇒ p₁ r₁) rs₁

  app₂ₐ* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app (lam e₁) e₂ ⇒* app (lam e₁) e₂′
  app₂ₐ* = map app₂ₐ

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map (app₂ p₁)

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
              e₁ SS.CBV.⇒* lam e₁′ → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ rs₂ p₂′ rs = cbv-app₁* rs₁ ◅◅ app₂ₐ* rs₂ ◅◅ applam* p₂′ ◅◅ rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
           e₁ SS.CBV.⇒* e₁′ → NAWNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁″ e₂′
  bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ = cbv-app₁* rs₁ ◅◅ app₁* p₁′ rs₁′ ◅◅ app₂* p₁″ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
  ss←bs var                 = ε
  ss←bs (lam r)             = bs-lam (ss←bs r)
  ss←bs (applam r₁ r₂ r)    = bs-applam (CBV.Lem-4-3-2.ss←bs r₁) (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
  ss←bs (app r₁ q₁′ r₁′ r₂) = bs-app (CBV.Lem-4-3-2.ss←bs r₁) p₁′ (ss←bs r₁′) p₁″ (ss←bs r₂)
    where
      p₁′ = nawnf←wnf (BS-CBV.wnf-⇓ r₁) q₁′
      p₁″ = nanf←nf (nf-⇓ r₁′) (na←wnf-⇓ (BS-CBV.wnf-⇓ r₁) q₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 4.5.3.  SS-HAO to NF and BS-HAO coincide

module Thm-4-5-3 where
  ss-hao↔bs-hao : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
  ss-hao↔bs-hao = uncurry Lem-4-5-1.bs←ss , λ r → Lem-4-5-2.ss←bs r , BS-HAO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
