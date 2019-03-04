---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-NO₊ where

open import Semantics-SmallStep
import Semantics-SmallStep-CBN as SS-CBN
open NO₊ public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam₋ ¬p r) → whnf←nf p ↯ ¬p
                      ; (_ , lam₊ p′ r) → (_ , r) ↯ nrf←nf p
                      }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , app₁₊ p₁′ r₁)     → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂₋ p₁′ ¬p₂ r₂) → (_ , r₂) ↯ SS-CBN.nrf←nf p₂
                            ; (_ , app₂₊ p₁′ p₂′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            }

det-⇒ : Deterministic′ _⇒_
det-⇒ (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ SS-CBN.det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam & SS-CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
det-⇒ (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
det-⇒ (lam₊ p r)        (lam₊ p′ r′)         = lam & det-⇒ r r′


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂₋ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂₊ p₁′ p₂ r₂)  = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app (naxnf-⇒ p₁ r₁))
whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
whnf-⇒ (app₂₊ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
whnf-⇒ (lam₋ ¬p r)       = lam
whnf-⇒ (lam₊ p r)        = lam


---------------------------------------------------------------------------------------------------------------

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app p₁)
rev-whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
rev-whnf-⇒ (app₂₊ p₁ p₂ r₂)  = whnf (app (naxnf←nanf p₁))
rev-whnf-⇒ (lam₋ ¬p r)       = lam
rev-whnf-⇒ (lam₊ p r)        = lam


---------------------------------------------------------------------------------------------------------------

cbn-app₂ : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ CBN.⇒ e₂′ → app e₁ e₂ ⇒ app e₁ e₂′
cbn-app₂ {e₂ = e₂} p₁ r₂ with whnf? e₂
... | no ¬p₂ = app₂₋ p₁ ¬p₂ r₂
... | yes p₂ = (_ , r₂) ↯ SS-CBN.nrf←whnf p₂

cbn-lam : ∀ {n} {e : Tm (suc n)} {e′} → e CBN.⇒ e′ → lam e ⇒ lam e′
cbn-lam {e = e} r with whnf? e
... | no ¬p = lam₋ ¬p r
... | yes p = (_ , r) ↯ SS-CBN.nrf←whnf p


---------------------------------------------------------------------------------------------------------------

app₂ : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒ e₂′ → app e₁ e₂ ⇒ app e₁ e₂′
app₂ p₁ r = app₂₊ p₁ (rev-whnf-⇒ r) r

lam′ : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒ e′ → lam e ⇒ lam e′
lam′ r = lam₊ (rev-whnf-⇒ r) r


---------------------------------------------------------------------------------------------------------------

cbn-app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ SS-CBN.⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
cbn-app₂* p₁ = map (cbn-app₂ p₁)

cbn-lam* : ∀ {n} {e : Tm (suc n)} {e′} → e SS-CBN.⇒* e′ → lam e ⇒* lam e′
cbn-lam* = map cbn-lam


---------------------------------------------------------------------------------------------------------------

app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁₊* p₁ ε          = ε
app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

app₂₊* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → WHNF e₂ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂₊* p₁ p₂ ε          = ε
app₂₊* p₁ p₂ (r₂ ◅ rs₂) = app₂₊ p₁ p₂ r₂ ◅ app₂₊* p₁ (whnf-⇒ r₂) rs₂

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

lam₊* : ∀ {n} {e : Tm (suc n)} {e′} → WHNF e → e ⇒* e′ → lam e ⇒* lam e′
lam₊* p ε        = ε
lam₊* p (r ◅ rs) = lam₊ p r ◅ lam₊* (whnf-⇒ r) rs

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam′


---------------------------------------------------------------------------------------------------------------

bs-lam : ∀ {n} {e : Tm (suc n)} {e′ e″} → e SS-CBN.⇒* e′ → e′ ⇒* e″ → lam e ⇒* lam e″
bs-lam rs rs′ = cbn-lam* rs ◅◅ lam* rs′

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e₂″} →
         NAXNF e₁ → e₁ ⇒* e₁′ → NANF e₁′ → e₂ SS-CBN.⇒* e₂′ → e₂′ ⇒* e₂″ →
         app e₁ e₂ ⇒* app e₁′ e₂″
bs-app p₁ rs₁ p₁′ rs₂ rs₂′ = app₁₊* p₁ rs₁ ◅◅ cbn-app₂* p₁′ rs₂ ◅◅ app₂* p₁′ rs₂′


---------------------------------------------------------------------------------------------------------------

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


---------------------------------------------------------------------------------------------------------------

¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
¬lam⇒*var = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*var
               ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*var
               }

¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
¬lam⇒*app = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*app
               ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*app
               }


---------------------------------------------------------------------------------------------------------------
