---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HNO and BS-HNO
--
--                    4.8.1
--      SS-HS|SS-HNO₂ ← SS-HNO ⎫       SS-HNO      ⎫     SS-HNO
--  4.6.1 ↓     ↓ 4.8.2         ⎬ 4.8.4 ↓   ↑ 4.8.5 ⎬ 4.8.6 ↕
--      BS-HS|BS-HNO₂ → BS-HNO ⎭       BS-HNO      ⎭     BS-HNO
--                    4.8.3

module 4-8-Equivalence-HNO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-6-Properties-SmallStep-HS as SS-HS
import 2-8-1-Properties-SmallStep-HNO as SS-HNO
import 2-8-2-Properties-SmallStep-HNO₂ as SS-HNO₂
import 3-6-Properties-BigStep-HS as BS-HS
import 3-8-1-Properties-BigStep-HNO as BS-HNO
import 3-8-2-Properties-BigStep-HNO₂ as BS-HNO₂
import 4-6-Equivalence-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.8.1.  SS-HNO to NF implies SS-HS to HNF followed by SS-HNO₂ to NF

module Lem-4-8-1 where
  open SS

  hs←hno : ∀ {n} {e : Tm n} {e′} → ¬ HNF e → e HNO.⇒ e′ → e HS.⇒ e′
  hs←hno ¬p (HNO.lam r)        = HS.lam (hs←hno (λ p → lam p ↯ ¬p) r)
  hs←hno ¬p (HNO.applam p₁)    = HS.applam p₁
  hs←hno ¬p (HNO.app₁ₐ ¬p₁ r₁) = HS.app₁ (HS.lam (hs←hno ¬p₁ r₁))
  hs←hno ¬p (HNO.app₁ p₁ r₁)   with hnf? _
  ... | no ¬p₁′                 = HS.app₁ (hs←hno ¬p₁′ r₁)
  ... | yes p₁′                 = hnf (app (naxnf←hnf p₁′ p₁)) ↯ ¬p
  hs←hno ¬p (HNO.app₂ p₁ r₂)   = hnf (app (naxnf←nanf p₁)) ↯ ¬p

  hno₂←hno : ∀ {n} {e : Tm n} {e′} → HNF e → e HNO.⇒ e′ → e HNO₂.⇒ e′
  hno₂←hno (lam p)        (HNO.lam r)           = HNO₂.lam₊ p (hno₂←hno p r)
  hno₂←hno (hnf var)      ()
  hno₂←hno (hnf (app ())) (HNO.applam p₁)
  hno₂←hno (hnf (app ())) (SS-HNO.app₁ₐ ¬p₁ r₁)
  hno₂←hno (hnf (app p₁)) (HNO.app₁ p₁′ r₁)     = HNO₂.app₁₊ p₁ (hno₂←hno (hnf p₁) r₁)
  hno₂←hno (hnf (app _))  (HNO.app₂ p₁ r₂)      with hnf? _
  ... | no ¬p₂                                   = HNO₂.app₂₋ p₁ ¬p₂ (hs←hno ¬p₂ r₂)
  ... | yes p₂                                   = HNO₂.app₂₊ p₁ p₂ (hno₂←hno p₂ r₂)

  hs|hno₂←hno : ∀ {n} {e : Tm n} {e′} → e HNO.⇒ e′ → (e HS.⇒ e′) ⊎ (e HNO₂.⇒ e′)
  hs|hno₂←hno r with hnf? _
  ... | no ¬p = inj₁ (hs←hno ¬p r)
  ... | yes p = inj₂ (hno₂←hno p r)

  hno₂←hno* : ∀ {n} {e : Tm n} {e′} → HNF e → e HNO.⇒* e′ → e HNO₂.⇒* e′
  hno₂←hno* p ε        = ε
  hno₂←hno* p (r ◅ rs) = hno₂←hno p r ◅ hno₂←hno* (SS-HNO₂.hnf-⇒ (hno₂←hno p r)) rs

  hs|hno₂←hno* : ∀ {n} {e : Tm n} {e′} → e HNO.⇒* e′ → NF e′ →
                  (∃ λ e″ →
                    e HS.⇒* e″ × HNF e″ × e″ HNO₂.⇒* e′)
  hs|hno₂←hno* ε        p′ = _ , ε , hnf←nf p′ , ε
  hs|hno₂←hno* (r ◅ rs) p′ with hs|hno₂←hno r
  ... | inj₂ r′             = _ , ε , SS-HNO₂.rev-hnf-⇒ r′ , r′ ◅ hno₂←hno* (SS-HNO₂.hnf-⇒ r′) rs
  ... | inj₁ r′             with hs|hno₂←hno* rs p′
  ... | _ , rs′ , p″ , rs″  = _ , r′ ◅ rs′ , p″ , rs″


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.8.2.  SS-HNO₂ to NF implies BS-HNO₂

module Lem-4-8-2 where
  open SS-HNO₂
  open BS-HNO₂

  rev-lam₊* : ∀ {n i} {e : Tm (suc n)} {e′} → HNF e → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
  rev-lam₊* p ε                = ε
  rev-lam₊* p (lam₊ p′ r ◅ rs) = r ◅ rev-lam₊* (hnf-⇒ r) rs

  ¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
  ¬lam⇒*var = λ { (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*var }

  ¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*app }

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
    bs←ss ε        p′ = refl-⇓ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
    bs←ss′ (lam₊ p r)        rs (lam p″)       = lam p (bs←ss′ r (rev-lam₊* (hnf-⇒ r) rs) p″)
    bs←ss′ (lam₊ p r)        rs (nf var)       = rs ↯ ¬lam⇒*var
    bs←ss′ (lam₊ p r)        rs (nf (app _ _)) = rs ↯ ¬lam⇒*app
    bs←ss′ (app₁₊ p₁ r₁)     rs p″             = {!!}
    bs←ss′ (app₂₋ p₁ ¬p₂ r₂) rs p″             = {!!}
    bs←ss′ (app₂₊ p₁ p₂ r₂)  rs p″             = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.8.3.  BS-HS followed by BS-HNO₂ implies BS-HNO

module Lem-4-8-3 where
  open BS

  hno←hs|hno₂ : ∀ {n} {e : Tm n} {e′ e″} → e HS.⇓ e′ → e′ HNO₂.⇓ e″ → e HNO.⇓ e″
  hno←hs|hno₂ HS.var           HNO₂.var                 = HNO.var
  hno←hs|hno₂ (HS.lam r)       (HNO₂.lam p r′)          = HNO.lam (hno←hs|hno₂ r r′)
  hno←hs|hno₂ (HS.applam r₁ r) r′                       = HNO.applam r₁ (hno←hs|hno₂ r r′)
  hno←hs|hno₂ (HS.app r₁ p₁′)  (HNO₂.app p₁ r₁′ r₂ r₂′) = HNO.app r₁ p₁′ r₁″ (hno←hs|hno₂ r₂ r₂′)
    where
      r₁″ = hno←hs|hno₂ (BS-HS.refl-⇓ (BS-HS.hnf-⇓ r₁)) r₁′


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 4.8.4.  SS-HNO to NF implies BS-HNO

module Cor-4-8-4 where
  open SS-HNO
  open BS-HNO

  bs←ss : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ → e ⇓ e′
  bs←ss rs p′             with Lem-4-8-1.hs|hno₂←hno* rs p′
  ... | _ , rs′ , p″ , rs″ = Lem-4-8-3.hno←hs|hno₂ (HS.Lem-4-6-1.bs←ss rs′ p″)
                                                    (Lem-4-8-2.bs←ss rs″ p′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.8.5.  BS-HNO implies SS-HNO

module Lem-4-8-5 where
  open SS-HNO
  open BS-HNO

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → HNF e₁ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₁ = applam p₁ ◅ ε

  hs-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.HS.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  hs-app₁* = map hs-app₁

  app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁₊* p₁ ε          = ε
  app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map (app₂ p₁)

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} →
              e₁ SS.HS.⇒* lam e₁′ → HNF (lam e₁′) → e₁′ [ e₂ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ (lam p₁′) rs = hs-app₁* rs₁ ◅◅ applam* p₁′ ◅◅ rs
  bs-applam rs₁ (hnf ())  rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
           e₁ SS.HS.⇒* e₁′ → NAXNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁″ e₂′
  bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ = hs-app₁* rs₁ ◅◅ app₁₊* p₁′ rs₁′ ◅◅ app₂* p₁″ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
  ss←bs var                 = ε
  ss←bs (lam r)             = bs-lam (ss←bs r)
  ss←bs (applam r₁ r)       = bs-applam (HS.Lem-4-6-2.ss←bs r₁) (BS-HS.hnf-⇓ r₁) (ss←bs r)
  ss←bs (app r₁ p₁′ r₁′ r₂) = bs-app (HS.Lem-4-6-2.ss←bs r₁) p₁″ (ss←bs r₁′) p₁‴ (ss←bs r₂)
    where
      p₁″ = naxnf←hnf (BS-HS.hnf-⇓ r₁) p₁′
      p₁‴ = nanf←nf (nf-⇓ r₁′) (na←hnf-⇓ (BS-HS.hnf-⇓ r₁) p₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 4.8.6.  SS-HNO to NF and BS-HNO coincide

module Thm-4-8-6 where
  ss-hno↔bs-hno : ∀ {n} {e : Tm n} {e′} → (e SS.HNO.⇒* e′ × NF e′) ↔ e BS.HNO.⇓ e′
  ss-hno↔bs-hno = uncurry Cor-4-8-4.bs←ss , λ r → Lem-4-8-5.ss←bs r , BS-HNO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
