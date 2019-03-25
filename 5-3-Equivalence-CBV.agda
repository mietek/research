---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-CBV and BS-CBV
--
--        SS-CBV      ⎫     SS-CBV
--  5.3.1 ↓   ↑ 5.3.2 ⎬ 5.3.3 ↕
--        BS-CBV      ⎭     BS-CBV

module 5-3-Equivalence-CBV where

open import 1-2-Syntax-Predicates
import 2-1-Semantics-BigStep as BS
import 2-2-Semantics-SmallStep as SS
import 3-3-Properties-BigStep-CBV as BS-CBV
import 4-3-Properties-SmallStep-CBV as SS-CBV


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.3.1.  SS-CBV to WHNF implies BS-CBV

module Lem-5-3-1 where
  open SS-CBV
  open BS-CBV

  rev-app* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
             app e₁ e₂ ⇒*⟨ i ⟩ e′ → WNF e′ →
             (∃³ λ s e₁′ e₂′ →
               e₁ ⇒*⟨ i ⟩ lam s e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
             (∃² λ e₁′ e₂′ →
               e₁ ⇒*⟨ i ⟩ e₁′ × NAWNF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × WNF e₂′ × app e₁′ e₂′ ≡ e′)
  rev-app* ε                      (wnf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
  rev-app* (applam p₂ ◅ rs)       p′                = inj₁ (_ , ε , ε , p₂ , rs)
  rev-app* (app₁ r₁ ◅ rs)         p′                with rev-app* rs p′
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)            = inj₁ (_ , r₁ ◅ rs₁ , rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)     = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂′ , refl)
  rev-app* (app₂ p₁ r₂ ◅ rs)      p′                with rev-app* rs p′
  ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)            = inj₁ (_ , rs₁ , r₂ ◅ rs₂ , p₂′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)     = inj₂ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , refl)

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → WNF e′ → e ⟱ e′
    bs←ss ε        p′ = refl-⟱ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → WNF e″ → e ⟱ e″
    bs←ss′ (applam p₂)  rs p″                    = applam lam (refl-⟱ p₂) (bs←ss rs p″)
    bs←ss′ (app₁ r₁)    rs p″                    with rev-app* rs p″
    ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss′ r₁ rs₁ lam) (bs←ss rs₂ p₂′)
                                                           (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss′ r₁ rs₁ (wnf p₁′)) (na←nawnf p₁′)
                                                        (bs←ss rs₂ p₂′)
    bs←ss′ (app₂ p₁ r₂) rs p″                    with rev-app* rs p″
    ... | inj₁ (_ , rs₁ , rs₂ , p₂′ , rs′)        = applam (bs←ss rs₁ lam) (bs←ss′ r₂ rs₂ p₂′)
                                                           (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl) = app (bs←ss rs₁ (wnf p₁′)) (na←nawnf p₁′)
                                                        (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.3.2.  BS-CBV implies SS-CBV

module Lem-5-3-2 where
  open SS-CBV
  open BS-CBV

  applam* : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} → WNF e₂ → app (lam s e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₂ = applam p₂ ◅ ε

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* = map* app₁

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → WNF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map* (app₂ p₁)

  bs-applam : ∀ {n s} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
              e₁ ⇒* lam s e₁′ → e₂ ⇒* e₂′ → WNF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ rs₂ p₂′ rs = app₁* rs₁ ◅◅ app₂* lam rs₂ ◅◅ applam* p₂′ ◅◅ rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
           e₁ ⇒* e₁′ → WNF e₁′ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁′ e₂′
  bs-app rs₁ p₁′ rs₂ = app₁* rs₁ ◅◅ app₂* p₁′ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → e ⇒* e′
  ss←bs (applam r₁ r₂ r) = bs-applam (ss←bs r₁) (ss←bs r₂) (wnf-⟱ r₂) (ss←bs r)
  ss←bs var              = ε
  ss←bs lam              = ε
  ss←bs (app r₁ p₁′ r₂)  = bs-app (ss←bs r₁) (wnf-⟱ r₁) (ss←bs r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 5.3.3.  SS-CBV to WNF and BS-CBV coincide

module Thm-5-3-3 where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → (e SS.CBV.⇒* e′ × WNF e′) ↔ e BS.CBV.⟱ e′
  ss↔bs = uncurry Lem-5-3-1.bs←ss , λ r → Lem-5-3-2.ss←bs r , BS-CBV.wnf-⟱ r


---------------------------------------------------------------------------------------------------------------
