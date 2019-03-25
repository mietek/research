---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-NO and BS-NO
--
--                    5.2.1
--      SS-CBN|SS-NO₂ ← SS-NO ⎫       SS-NO       ⎫     SS-NO
--  5.1.1 ↓      ↓ 5.2.2       ⎬ 5.2.4 ↓   ↑ 5.2.5 ⎬ 5.2.6 ↕
--      BS-CBN|BS-NO₂ → BS-NO ⎭       BS-NO       ⎭     BS-NO
--                    5.2.3

module 5-2-Equivalence-NO where

open import 1-2-Syntax-Predicates
import 2-1-Semantics-BigStep as BS
import 2-2-Semantics-SmallStep as SS
import 3-1-Properties-BigStep-CBN as BS-CBN
import 3-2-Properties-BigStep-NO as BS-NO
import 3-2-1-Properties-BigStep-NO₂ as BS-NO₂
import 4-1-Properties-SmallStep-CBN as SS-CBN
import 4-2-Properties-SmallStep-NO as SS-NO
import 4-2-1-Properties-SmallStep-NO₂ as SS-NO₂
open import 5-1-Equivalence-CBN


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.2.1.  SS-NO to NF implies SS-CBN to WHNF followed by SS-NO₂ to NF

module Lem-5-2-1 where
  open SS

  cbn←no : ∀ {n} {e : Tm n} {e′} → ¬ WHNF e → e NO.⇒ e′ → e CBN.⇒ e′
  cbn←no ¬p NO.applam       = CBN.applam
  cbn←no ¬p (NO.lam r)      = lam ↯ ¬p
  cbn←no ¬p (NO.app₁ p₁ r₁) with whnf? _
  ... | no ¬p₁′              = CBN.app₁ (cbn←no ¬p₁′ r₁)
  ... | yes p₁′              = whnf (app (naxnf←whnf p₁′ p₁)) ↯ ¬p
  cbn←no ¬p (NO.app₂ p₁ r₂) = whnf (app (naxnf←nanf p₁)) ↯ ¬p

  no₂←no : ∀ {n} {e : Tm n} {e′} → WHNF e → e NO.⇒ e′ → e NO₂.⇒ e′
  no₂←no lam             (NO.lam r)       with whnf? _
  ... | no ¬p                              = NO₂.cbn-lam ¬p (cbn←no ¬p r)
  ... | yes p                              = NO₂.lam p (no₂←no p r)
  no₂←no (whnf var)      ()
  no₂←no (whnf (app ())) NO.applam
  no₂←no (whnf (app p₁)) (NO.app₁ p₁′ r₁) = NO₂.app₁ p₁ (no₂←no (whnf p₁) r₁)
  no₂←no (whnf (app _))  (NO.app₂ p₁ r₂)  with whnf? _
  ... | no ¬p₂                             = NO₂.cbn-app₂ p₁ ¬p₂ (cbn←no ¬p₂ r₂)
  ... | yes p₂                             = NO₂.app₂ p₁ p₂ (no₂←no p₂ r₂)

  cbn|no₂←no : ∀ {n} {e : Tm n} {e′} → e NO.⇒ e′ → (e CBN.⇒ e′) ⊎ (e NO₂.⇒ e′)
  cbn|no₂←no r with whnf? _
  ... | no ¬p = inj₁ (cbn←no ¬p r)
  ... | yes p = inj₂ (no₂←no p r)

  no₂←no* : ∀ {n} {e : Tm n} {e′} → WHNF e → e NO.⇒* e′ → e NO₂.⇒* e′
  no₂←no* p ε        = ε
  no₂←no* p (r ◅ rs) = no₂←no p r ◅ no₂←no* (SS-NO₂.whnf-⇒ (no₂←no p r)) rs

  cbn|no₂←no* : ∀ {n} {e : Tm n} {e′} → e NO.⇒* e′ → NF e′ →
                 (∃ λ e″ →
                   e CBN.⇒* e″ × WHNF e″ × e″ NO₂.⇒* e′)
  cbn|no₂←no* ε        p′ = _ , ε , whnf←nf p′ , ε
  cbn|no₂←no* (r ◅ rs) p′ with cbn|no₂←no r
  ... | inj₂ r′            = _ , ε , SS-NO₂.rev-whnf-⇒ r′ , r′ ◅ no₂←no* (SS-NO₂.whnf-⇒ r′) rs
  ... | inj₁ r′            with cbn|no₂←no* rs p′
  ... | _ , rs′ , p″ , rs″ = _ , r′ ◅ rs′ , p″ , rs″


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.2.2.  SS-NO₂ to NF implies BS-NO₂

module Lem-5-2-2 where
  open BS-NO₂
  open SS-NO₂

  rev-lam* : ∀ {n i s} {e : Tm (suc n)} {e′} → WHNF e → lam s e ⇒*⟨ i ⟩ lam s e′ → e ⇒*⟨ i ⟩ e′
  rev-lam* p ε                   = ε
  rev-lam* p (cbn-lam ¬p r ◅ rs) = p ↯ ¬p
  rev-lam* p (lam p′ r ◅ rs)     = r ◅ rev-lam* (whnf-⇒ r) rs

  rev-cbn-lam* : ∀ {n i s} {e : Tm (suc n)} {e′} →
                 lam s e ⇒*⟨ i ⟩ lam s e′ → NF e′ →
                 (∃ λ e″ →
                   e SS.CBN.⇒*⟨ i ⟩ e″ × WHNF e″ × e″ ⇒* e′)
  rev-cbn-lam* ε                   p′ = _ , ε , whnf←nf p′ , ε
  rev-cbn-lam* (cbn-lam ¬p r ◅ rs) p′ with rev-cbn-lam* rs p′
  ... | _ , rs′ , p″ , rs″            = _ , r ◅ rs′ , p″ , rs″
  rev-cbn-lam* (lam p r ◅ rs)      p′ = _ , ε , p , r ◅ rev-lam* (whnf-⇒ r) rs

  ¬lam⇒*var : ∀ {n s} {e : Tm (suc n)} {s′ x} → ¬ (lam s e ⇒* var s′ x)
  ¬lam⇒*var = λ { (cbn-lam ¬p r ◅ rs) → rs ↯ ¬lam⇒*var
                 ; (lam p r ◅ rs)      → rs ↯ ¬lam⇒*var }

  ¬lam-s⇒*lam-s′ : ∀ {n s} {e : Tm (suc n)} {s′ e′} → s ≢ s′ → ¬ (lam s e ⇒* lam s′ e′)
  ¬lam-s⇒*lam-s′ s≢s′ = λ { ε                   → refl ↯ s≢s′
                           ; (cbn-lam ¬p r ◅ rs) → rs ↯ ¬lam-s⇒*lam-s′ s≢s′
                           ; (lam p r ◅ rs)      → rs ↯ ¬lam-s⇒*lam-s′ s≢s′ }

  ¬lam⇒*app : ∀ {n s} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam s e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (cbn-lam ¬p r ◅ rs) → rs ↯ ¬lam⇒*app
                 ; (lam p r ◅ rs)      → rs ↯ ¬lam⇒*app }

  rev-app₂* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              NANF e₁ → WHNF e₂ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃ λ e₂′ →
                e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁ e₂′ ≡ e′)
  rev-app₂* p₁ p₂ ε                          (nf (app p₁′ p₂′)) = _ , ε , p₂′ , refl
  rev-app₂* p₁ p₂ (app₁ p₁′ r₁ ◅ rs)         p′                 = r₁ ↯ nrf←nanf p₁
  rev-app₂* p₁ p₂ (cbn-app₂ p₁′ ¬p₂ r₂ ◅ rs) p′                 = p₂ ↯ ¬p₂
  rev-app₂* p₁ p₂ (app₂ p₁′ p₂′ r₂ ◅ rs)     p′                 with rev-app₂* p₁′ (whnf-⇒ r₂) rs p′
  ... | _ , rs₂ , p₂″ , refl                                    = _ , r₂ ◅ rs₂ , p₂″ , refl

  rev-cbn-app₂* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
                  NANF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
                  (∃² λ e₂′ e₂″ →
                    e₂ SS.CBN.⇒*⟨ i ⟩ e₂′ × WHNF e₂′ × e₂′ ⇒*⟨ i ⟩ e₂″ × NF e₂″ × app e₁ e₂″ ≡ e′)
  rev-cbn-app₂* p₁ ε                          (nf (app p₁′ p₂′)) = _ , ε , whnf←nf p₂′ , ε , p₂′ , refl
  rev-cbn-app₂* p₁ (app₁ p₁′ r₁ ◅ rs)         p′                 = r₁ ↯ nrf←nanf p₁
  rev-cbn-app₂* p₁ (cbn-app₂ p₁′ ¬p₂ r₂ ◅ rs) p′                 with rev-cbn-app₂* p₁′ rs p′
  ... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl                         = _ , r₂ ◅ rs₂ , p₂ , rs₂′ , p₂′ , refl
  rev-cbn-app₂* p₁ (app₂ p₁′ p₂ r₂ ◅ rs)      p′                 with rev-app₂* p₁′ (whnf-⇒ r₂) rs p′
  ... | _ , rs₂ , p₂′ , refl                                     = _ , ε , p₂ , r₂ ◅ rs₂ , p₂′ , refl

  rev-app₁* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
              app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
              (∃³ λ e₁′ e₂′ e₂″ →
                e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ SS.CBN.⇒*⟨ i ⟩ e₂′ × WHNF e₂′ ×
                e₂′ ⇒*⟨ i ⟩ e₂″ × NF e₂″ × app e₁′ e₂″ ≡ e′)
  rev-app₁* ε                         (nf (app p₁′ p₂′)) = _ , ε , p₁′ , ε , whnf←nf p₂′ , ε , p₂′ , refl
  rev-app₁* (app₁ p₁ r₁ ◅ rs)         p′                 with rev-app₁* rs p′
  ... | _ , rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl     = _ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl
  rev-app₁* (cbn-app₂ p₁ ¬p₂ r₂ ◅ rs) p′                 with rev-cbn-app₂* p₁ rs p′
  ... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl                 = _ , ε , p₁ , r₂ ◅ rs₂ , p₂ , rs₂′ , p₂′ , refl
  rev-app₁* (app₂ p₁ p₂ r₂ ◅ rs)      p′                 with rev-app₂* p₁ (whnf-⇒ r₂) rs p′
  ... | _ , rs₂ , p₂′ , refl                             = _ , ε , p₁ , ε , p₂ , r₂ ◅ rs₂ , p₂′ , refl

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⟱ e′
    bs←ss ε        p′ = refl-⟱ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⟱ e″
    bs←ss′ (cbn-lam {s = s} ¬p r) rs (lam {s = s′} p″) with s ≟ s′
    ... | no s≢s′                                       = rs ↯ ¬lam-s⇒*lam-s′ s≢s′
    ... | yes refl                                      with rev-cbn-lam* rs p″
    ... | _ , rs′ , p′ , rs″                            = lam (Lem-5-1-1.bs←ss′ r rs′ p′)
                                                              (bs←ss rs″ p″)
    bs←ss′ (cbn-lam ¬p r)         rs (nf var)          = rs ↯ ¬lam⇒*var
    bs←ss′ (cbn-lam ¬p r)         rs (nf (app _ _))    = rs ↯ ¬lam⇒*app
    bs←ss′ (lam {s = s} p r)      rs (lam {s = s′} p″) with s ≟ s′
    ... | no s≢s′                                       = rs ↯ ¬lam-s⇒*lam-s′ s≢s′
    ... | yes refl                                      = lam (BS-CBN.refl-⟱ p)
                                                              (bs←ss′ r (rev-lam* (whnf-⇒ r) rs) p″)
    bs←ss′ (lam p r)              rs (nf var)          = rs ↯ ¬lam⇒*var
    bs←ss′ (lam p r)              rs (nf (app _ _))    = rs ↯ ¬lam⇒*app
    bs←ss′ (app₁ p₁ r₁)           rs p″                with rev-app₁* rs p″
    ... | _ , rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl  = app p₁ (bs←ss′ r₁ rs₁ (nf p₁′))
                                                              (Lem-5-1-1.bs←ss rs₂ p₂)
                                                              (bs←ss rs₂′ p₂′)
    bs←ss′ (cbn-app₂ p₁ ¬p₂ r₂)   rs p″                with rev-cbn-app₂* p₁ rs p″
    ... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl              = app (naxnf←nanf p₁) (refl-⟱′ p₁)
                                                              (Lem-5-1-1.bs←ss′ r₂ rs₂ p₂)
                                                              (bs←ss rs₂′ p₂′)
    bs←ss′ (app₂ p₁ p₂ r₂)        rs p″                with rev-app₂* p₁ (whnf-⇒ r₂) rs p″
    ... | _ , rs₂ , p₂′ , refl                          = app (naxnf←nanf p₁) (refl-⟱′ p₁)
                                                              (BS-CBN.refl-⟱ p₂)
                                                              (bs←ss′ r₂ rs₂ p₂′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.2.3.  BS-CBN followed by BS-NO₂ implies BS-NO

module Lem-5-2-3 where
  open BS

  no←cbn|no₂ : ∀ {n} {e : Tm n} {e′ e″} → e CBN.⟱ e′ → e′ NO₂.⟱ e″ → e NO.⟱ e″
  no←cbn|no₂ (CBN.applam r₁ r) r′                      = NO.applam r₁ (no←cbn|no₂ r r′)
  no←cbn|no₂ CBN.var           NO₂.var                 = NO.var
  no←cbn|no₂ CBN.lam           (NO₂.lam r r′)          = NO.lam (no←cbn|no₂ r r′)
  no←cbn|no₂ (CBN.app r₁ p₁′)  (NO₂.app p₁ r₁′ r₂ r₂′) = NO.app r₁ p₁′ r₁″ (no←cbn|no₂ r₂ r₂′)
    where
      r₁″ = no←cbn|no₂ (BS-CBN.refl-⟱ (BS-CBN.whnf-⟱ r₁)) r₁′


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 5.2.4.  SS-NO to NF implies BS-NO

module Cor-5-2-4 where
  open SS-NO
  open BS-NO

  bs←ss : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ → e ⟱ e′
  bs←ss rs p′             with Lem-5-2-1.cbn|no₂←no* rs p′
  ... | _ , rs′ , p″ , rs″ = Lem-5-2-3.no←cbn|no₂ (Lem-5-1-1.bs←ss rs′ p″)
                                                   (Lem-5-2-2.bs←ss rs″ p′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.2.5.  BS-NO implies SS-NO

module Lem-5-2-5 where
  open SS-NO
  open BS-NO

  applam* : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam s e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* = applam ◅ ε

  lam* : ∀ {n s} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam s e ⇒* lam s e′
  lam* = map* lam

  cbn-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBN.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  cbn-app₁* = map* cbn-app₁

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* p₁ ε          = ε
  app₁* p₁ (r₁ ◅ rs₁) = app₁ (na←naxnf p₁) r₁ ◅ app₁* (naxnf-⇒ p₁ r₁) rs₁

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map* (app₂ p₁)

  bs-applam : ∀ {n s} {e₁ e₂ : Tm n} {e₁′ e′} →
              e₁ SS.CBN.⇒* lam s e₁′ → e₁′ [ e₂ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ rs = cbn-app₁* rs₁ ◅◅ applam* ◅◅ rs

  bs-lam : ∀ {n s} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam s e ⇒* lam s e′
  bs-lam = lam*

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
           e₁ SS.CBN.⇒* e₁′ → NAXNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁″ e₂′
  bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ = cbn-app₁* rs₁ ◅◅ app₁* p₁′ rs₁′ ◅◅ app₂* p₁″ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → e ⇒* e′
  ss←bs (applam r₁ r)       = bs-applam (Lem-5-1-2.ss←bs r₁) (ss←bs r)
  ss←bs var                 = ε
  ss←bs (lam r)             = bs-lam (ss←bs r)
  ss←bs (app r₁ p₁′ r₁′ r₂) = bs-app (Lem-5-1-2.ss←bs r₁) p₁″ (ss←bs r₁′) p₁‴ (ss←bs r₂)
    where
      p₁″ = naxnf←whnf (BS-CBN.whnf-⟱ r₁) p₁′
      p₁‴ = nanf←nf (nf-⟱ r₁′) (na←whnf-⟱ (BS-CBN.whnf-⟱ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 5.2.6.  SS-NO to NF and BS-NO coincide

module Thm-5-2-6 where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → (e SS.NO.⇒* e′ × NF e′) ↔ e BS.NO.⟱ e′
  ss↔bs = uncurry Cor-5-2-4.bs←ss , λ r → Lem-5-2-5.ss←bs r , BS-NO.nf-⟱ r


---------------------------------------------------------------------------------------------------------------
