---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HS and BS-HS
--
--        SS-HS       ⎫     SS-HS
--  4.6.1 ↓   ↑ 4.6.2 ⎬ 4.6.3 ↕
--        BS-HS       ⎭     BS-HS

module 4-6-Equivalence-HS where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-6-Properties-SmallStep-HS as SS-HS
import 3-6-Properties-BigStep-HS as BS-HS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.6.1.  SS-HS to HNF implies BS-HS

module Lem-4-6-1 where
  open SS-HS
  open BS-HS

  rev-lam* : ∀ {n i} {e : Tm (suc n)} {e′} → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
  rev-lam* ε            = ε
  rev-lam* (lam r ◅ rs) = r ◅ rev-lam* rs

  ¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
  ¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

  ¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }

  rev-app₁* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → HNF e′ →
              (∃ λ e₁′ →
                e₁ ⇒*⟨ i ⟩ lam e₁′ × HNF e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
              (∃ λ e₁′ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NAXNF e₁′ × app e₁′ e₂ ≡ e′)
  rev-app₁* ε                (hnf (app p₁)) = inj₂ (_ , ε , p₁ , refl)
  rev-app₁* (applam p₁ ◅ rs) p′             = inj₁ (_ , ε , p₁ , rs)
  rev-app₁* (app₁ r₁ ◅ rs)   p′             with rev-app₁* rs p′
  ... | inj₁ (_ , rs₁ , p₁′ , rs′)          = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , rs′)
  ... | inj₂ (_ , rs₁ , p₁′ , refl)         = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → HNF e′ → e ⇓ e′
    bs←ss ε        p′ = refl-⇓ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → HNF e″ → e ⇓ e″
    bs←ss′ (lam r)     rs (lam p″)      = lam (bs←ss′ r (rev-lam* rs) p″)
    bs←ss′ (lam r)     rs (hnf var)     = rs ↯ ¬lam⇒*var
    bs←ss′ (lam r)     rs (hnf (app _)) = rs ↯ ¬lam⇒*app
    bs←ss′ (applam p₁) rs p″            = applam (refl-⇓ (lam p₁)) (bs←ss rs p″)
    bs←ss′ (app₁ r₁)   rs p″            with rev-app₁* rs p″
    ... | inj₁ (_ , rs₁ , p₁′ , rs′)     = applam (bs←ss′ r₁ rs₁ (lam p₁′)) (bs←ss rs′ p″)
    ... | inj₂ (_ , rs₁ , p₁′ , refl)    = app (bs←ss′ r₁ rs₁ (hnf p₁′)) (na←naxnf p₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.6.2.  BS-HS implies SS-HS

module Lem-4-6-2 where
  open SS-HS
  open BS-HS

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → HNF e₁ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₁ = applam p₁ ◅ ε

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* = map app₁

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
-- Theorem 4.6.3.  SS-HS to HNF and BS-HS coincide

module Thm-4-6-3 where
  ss-hs↔bs-hs : ∀ {n} {e : Tm n} {e′} → (e SS.HS.⇒* e′ × HNF e′) ↔ e BS.HS.⇓ e′
  ss-hs↔bs-hs = uncurry Lem-4-6-1.bs←ss , λ r → Lem-4-6-2.ss←bs r , BS-HS.hnf-⇓ r


---------------------------------------------------------------------------------------------------------------
