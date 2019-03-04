---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep-NO₊ where

open import Semantics-BigStep
open NO₊ public
open import Semantics-SmallStep-NO₊
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO₊ goes from WHNF to NF

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                = var
na←naxnf-⇓ (app p₁) (app q₁ r₁ r₂ r₂′) = app

na←whnf-⇓ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⇓ e′ → NA e′
na←whnf-⇓ lam      () r
na←whnf-⇓ (whnf p) q  r = na←naxnf-⇓ p r

rev-whnf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → WHNF e
rev-whnf-⇓ var                = whnf var
rev-whnf-⇓ (lam r r′)         = lam
rev-whnf-⇓ (app q₁ r₁ r₂ r₂′) = whnf (app (naxnf←whnf (rev-whnf-⇓ r₁) q₁))

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r r′)         = lam (nf-⇓ r′)
nf-⇓ (app q₁ r₁ r₂ r₂′) = nf (app (nanf←nf (nf-⇓ r₁) (na←whnf-⇓ (rev-whnf-⇓ r₁) q₁ r₁)) (nf-⇓ r₂′))


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO₊ is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (BS-CBN.refl-⇓ (whnf←nf p)) (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (na←nanf p₁) (refl-⇓ (nf p₁)) (BS-CBN.refl-⇓ (whnf←nf p₂)) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO₊ implies SS-NO₊

bs-lam : ∀ {n} {e : Tm (suc n)} {e′ e″} → e SS-CBN.⇒* e′ → e′ ⇒* e″ → lam e ⇒* lam e″
bs-lam rs rs′ = cbn-lam* rs ◅◅ lam* rs′

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e₂″} →
         NAXNF e₁ → e₁ ⇒* e₁′ → NANF e₁′ → e₂ SS-CBN.⇒* e₂′ → e₂′ ⇒* e₂″ →
         app e₁ e₂ ⇒* app e₁′ e₂″
bs-app p₁ rs₁ p₁′ rs₂ rs₂′ = app₁₊* p₁ rs₁ ◅◅ cbn-app₂* p₁′ rs₂ ◅◅ app₂* p₁′ rs₂′

ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
ss←bs var                = ε
ss←bs (lam r r′)         = bs-lam (BS-CBN.ss←bs r) (ss←bs r′)
ss←bs (app q₁ r₁ r₂ r₂′) = bs-app p₁ (ss←bs r₁) p₁′ (BS-CBN.ss←bs r₂) (ss←bs r₂′)
  where
    p₁  = naxnf←whnf (rev-whnf-⇓ r₁) q₁
    p₁′ = nanf←nf (nf-⇓ r₁) (na←whnf-⇓ (rev-whnf-⇓ r₁) q₁ r₁)


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₊ to NF implies BS-NO₊

rev-app₂₊-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
                NANF e₁ → WHNF e₂ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
                (∃ λ e₂′ → e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ × app e₁ e₂′ ≡ e′)
rev-app₂₊-⇒* p₁ p₂ ε                       (nf (app p₁′ p₂′)) = _ , ε , p₂′ , refl
rev-app₂₊-⇒* p₁ p₂ (app₁₊ p₁′ r₁ ◅ rs)     p′                 = (_ , r₁) ↯ nrf←nanf p₁
rev-app₂₊-⇒* p₁ p₂ (app₂₋ p₁′ ¬p₂ r₂ ◅ rs) p′                 = p₂ ↯ ¬p₂
rev-app₂₊-⇒* p₁ p₂ (app₂₊ p₁′ p₂′ r₂ ◅ rs) p′                 with rev-app₂₊-⇒* p₁′ (whnf-⇒ r₂) rs p′
... | _ , rs₂ , p₂″ , refl                                     = _ , r₂ ◅ rs₂ , p₂″ , refl

rev-app₂₋-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
                NANF e₁ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
                (∃² λ e₂′ e₂″ → e₂ SS-CBN.⇒*⟨ i ⟩ e₂′ × WHNF e₂′ × e₂′ ⇒*⟨ i ⟩ e₂″ × NF e₂″ ×
                  app e₁ e₂″ ≡ e′)
rev-app₂₋-⇒* p₁ ε                       (nf (app p₁′ p₂′)) = _ , ε , whnf←nf p₂′ , ε , p₂′ , refl
rev-app₂₋-⇒* p₁ (app₁₊ p₁′ r₁ ◅ rs)     p′                 = (_ , r₁) ↯ nrf←nanf p₁
rev-app₂₋-⇒* p₁ (app₂₋ p₁′ ¬p₂ r₂ ◅ rs) p′                 with rev-app₂₋-⇒* p₁′ rs p′
... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl                      = _ , r₂ ◅ rs₂ , p₂ , rs₂′ , p₂′ , refl
rev-app₂₋-⇒* p₁ (app₂₊ p₁′ p₂ r₂ ◅ rs)  p′                 with rev-app₂₊-⇒* p₁′ (whnf-⇒ r₂) rs p′
... | _ , rs₂ , p₂′ , refl                                  = _ , ε , p₂ , r₂ ◅ rs₂ , p₂′ , refl

rev-app₁₊-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
                app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
                (∃³ λ e₁′ e₂′ e₂″ → e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ SS-CBN.⇒*⟨ i ⟩ e₂′ × WHNF e₂′ ×
                  e₂′ ⇒*⟨ i ⟩ e₂″ × NF e₂″ × app e₁′ e₂″ ≡ e′)
rev-app₁₊-⇒* ε                      (nf (app p₁′ p₂′)) = _ , ε , p₁′ , ε , whnf←nf p₂′ , ε , p₂′ , refl
rev-app₁₊-⇒* (app₁₊ p₁ r₁ ◅ rs)     p′                 with rev-app₁₊-⇒* rs p′
... | _ , rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl      = _ , r₁ ◅ rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl
rev-app₁₊-⇒* (app₂₋ p₁ ¬p₂ r₂ ◅ rs) p′                 with rev-app₂₋-⇒* p₁ rs p′
... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl                  = _ , ε , p₁ , r₂ ◅ rs₂ , p₂ , rs₂′ , p₂′ , refl
rev-app₁₊-⇒* (app₂₊ p₁ p₂ r₂ ◅ rs)  p′                 with rev-app₂₊-⇒* p₁ (whnf-⇒ r₂) rs p′
... | _ , rs₂ , p₂′ , refl                              = _ , ε , p₁ , ε , p₂ , r₂ ◅ rs₂ , p₂′ , refl

rev-lam₊-⇒* : ∀ {n i} {e : Tm (suc n)} {e′} →
               WHNF e →
               lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
rev-lam₊-⇒* p ε                = ε
rev-lam₊-⇒* p (lam₋ ¬p r ◅ rs) = p ↯ ¬p
rev-lam₊-⇒* p (lam₊ p′ r ◅ rs) = r ◅ rev-lam₊-⇒* (whnf-⇒ r) rs

rev-lam₋-⇒* : ∀ {n i} {e : Tm (suc n)} {e′} →
               lam e ⇒*⟨ i ⟩ lam e′ → NF e′ →
               (∃ λ e″ → e SS-CBN.⇒*⟨ i ⟩ e″ × WHNF e″ × e″ ⇒* e′)
rev-lam₋-⇒* ε                p′ = _ , ε , whnf←nf p′ , ε
rev-lam₋-⇒* (lam₋ ¬p r ◅ rs) p′ with rev-lam₋-⇒* rs p′
... | _ , rs′ , p″ , rs″         = _ , r ◅ rs′ , p″ , rs″
rev-lam₋-⇒* (lam₊ p r ◅ rs)  p′ = _ , ε , p , r ◅ rev-lam₊-⇒* (whnf-⇒ r) rs

¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
¬lam⇒*var = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*var
               ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*var
               }

¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
¬lam⇒*app = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*app
               ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*app
               }

mutual
  bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → NF e′ → e ⇓ e′
  bs←ss ε        p′ = refl-⇓ p′
  bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

  bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → NF e″ → e ⇓ e″
  bs←ss′ (app₁₊ p₁ r₁)     rs p″                    with rev-app₁₊-⇒* rs p″
  ... | _ , rs₁ , p₁′ , rs₂ , p₂ , rs₂′ , p₂′ , refl = app (na←naxnf p₁) (bs←ss′ r₁ rs₁ (nf p₁′))
                                                           (BS-CBN.bs←ss rs₂ p₂) (bs←ss rs₂′ p₂′)
  bs←ss′ (app₂₋ p₁ ¬p₂ r₂) rs p″                    with rev-app₂₋-⇒* p₁ rs p″
  ... | _ , rs₂ , p₂ , rs₂′ , p₂′ , refl             = app (na←nanf p₁) (refl-⇓ (nf p₁))
                                                           (BS-CBN.bs←ss′ r₂ rs₂ p₂) (bs←ss rs₂′ p₂′)
  bs←ss′ (app₂₊ p₁ p₂ r₂)  rs p″                    with rev-app₂₊-⇒* p₁ (whnf-⇒ r₂) rs p″
  ... | _ , rs₂ , p₂′ , refl                         = app (na←nanf p₁) (refl-⇓ (nf p₁))
                                                           (BS-CBN.refl-⇓ p₂) (bs←ss′ r₂ rs₂ p₂′)
  bs←ss′ (lam₋ ¬p r)       rs (lam p″)              with rev-lam₋-⇒* rs p″
  ... | _ , rs′ , p′ , rs″                           = lam (BS-CBN.bs←ss′ r rs′ p′) (bs←ss rs″ p″)
  bs←ss′ (lam₋ ¬p r)       rs (nf var)              = rs ↯ ¬lam⇒*var
  bs←ss′ (lam₋ ¬p r)       rs (nf (app _ _))        = rs ↯ ¬lam⇒*app
  bs←ss′ (lam₊ p r)        rs (lam p″)              with rev-lam₊-⇒* (whnf-⇒ r) rs
  ... | rs′                                          = lam (BS-CBN.refl-⇓ p) (bs←ss′ r rs′ p″)
  bs←ss′ (lam₊ p r)        rs (nf var)              = rs ↯ ¬lam⇒*var
  bs←ss′ (lam₊ p r)        rs (nf (app _ _))        = rs ↯ ¬lam⇒*app


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO₊ and SS-NO₊ to NF coincide

bs↔ss : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ ↔ (e ⇒* e′ × NF e′)
bs↔ss = (λ r → ss←bs r , nf-⇓ r) , uncurry bs←ss


---------------------------------------------------------------------------------------------------------------
