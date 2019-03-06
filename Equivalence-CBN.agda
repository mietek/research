---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-CBN and BS-CBN
--
--      SS-CBN    ⎫   SS-CBN
--  1.1 ↓ × ↑ 1.2 ⎬ 1.3 ↕
--      BS-CBN    ⎭   BS-CBN

module Equivalence-CBN where

open import Syntax-Predicates
import Semantics-SmallStep as SS
import Semantics-BigStep as BS
import Properties-SmallStep-CBN as SS-CBN
import Properties-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 1.1.  SS-CBN to WHNF implies BS-CBN

module Lem-1-1 where
  open SS-CBN
  open BS-CBN

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
-- Lemma 1.2.  BS-CBN implies SS-CBN

module Lem-1-2 where
  open SS-CBN
  open BS-CBN

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* = applam ◅ ε

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* = map app₁

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
-- Theorem 1.3.  SS-CBN to WHNF and BS-CBN coincide

module Thm-1-3 where
  ss-cbn↔bs-cbn : ∀ {n} {e : Tm n} {e′} → (e SS.CBN.⇒* e′ × WHNF e′) ↔ e BS.CBN.⇓ e′
  ss-cbn↔bs-cbn = uncurry Lem-1-1.bs←ss , λ r → Lem-1-2.ss←bs r , BS-CBN.whnf-⇓ r


---------------------------------------------------------------------------------------------------------------
