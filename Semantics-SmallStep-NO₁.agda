---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-NO₁ where

open import Semantics-SmallStep
open NO₁ public
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-SmallStep-NO as SS-NO
import Semantics-SmallStep-NO₂ as SS-NO₂


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₁ does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam)       → case p₁ of λ ()
                            ; (_ , app₁₋ ¬p₁ r₁) → whnf←nf (nf p₁) ↯ ¬p₁
                            ; (_ , app₁₊ p₁′ r₁) → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁′ r₂)  → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₁ is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)        (lam r′)         = lam & det-⇒ r r′
det-⇒ applam         applam           = refl
det-⇒ applam         (app₁₋ ¬p₁′ r₁′) = lam ↯ ¬p₁′
det-⇒ applam         (app₁₊ () r₁′)
det-⇒ applam         (app₂ () r₂′)
det-⇒ (app₁₋ ¬p₁ r₁) applam           = lam ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁) (app₁₋ ¬p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₋ ¬p₁ r₁) (app₁₊ p₁′ r₁′)  = whnf p₁′ ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁) (app₂ p₁′ r₂′)   = whnf←nf (nf p₁′) ↯ ¬p₁
det-⇒ (app₁₊ () r₁)  applam
det-⇒ (app₁₊ p₁ r₁)  (app₁₋ ¬p₁′ r₁′) = whnf p₁ ↯ ¬p₁′
det-⇒ (app₁₊ p₁ r₁)  (app₁₊ p₁′ r₁′)  = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)  (app₂ p₁′ r₂′)   = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂)   applam
det-⇒ (app₂ p₁ r₂)   (app₁₋ ¬p₁′ r₁′) = whnf←nf (nf p₁) ↯ ¬p₁′
det-⇒ (app₂ p₁ r₂)   (app₁₊ p₁′ r₁′)  = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂)   (app₂ p₁′ r₂′)   = app & refl ⊗ det-⇒ r₂ r₂′

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₁ preserves NF and WHNF

mutual
  nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
  nf-⇒ (lam p) (lam r) = lam (nf-⇒ p r)
  nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)

  nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
  nanf-⇒ var         ()
  nanf-⇒ (app () p₂) applam
  nanf-⇒ (app p₁ p₂) (app₁₋ ¬p₁ r₁) = app (nanf-⇒ p₁ r₁) p₂
  nanf-⇒ (app p₁ p₂) (app₁₊ p₁′ r₁) = app (nanf-⇒ p₁ r₁) p₂
  nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂)  = app p₁′ (nf-⇒ p₂ r₂)

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁₋ ¬p₁ r₁) = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₁₊ p₁′ r₁) = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂ p₁′ r₂)  = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      (lam r) = lam
whnf-⇒ (whnf p) r       = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-NO₁ and SS-NO

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁₋ (λ { (whnf (app ())) }) applam
cbn-app₁ (CBN.app₁ r₁) with naxnf? _
... | no ¬p₁           = app₁₋ (λ { (whnf p₁) → p₁ ↯ ¬p₁ }) (cbn-app₁ r₁)
... | yes p₁           = app₁₊ p₁ (cbn-app₁ r₁)

app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NA e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁ var ()
app₁ app r  with naxnf? _
... | no ¬p₁ = app₁₋ (λ { (whnf p₁) → p₁ ↯ ¬p₁ }) r
... | yes p₁ = app₁₊ p₁ r

no₁←cbn-⇒ : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
no₁←cbn-⇒ CBN.applam    = applam
no₁←cbn-⇒ (CBN.app₁ r₁) = cbn-app₁ r₁

cbn←no₁-⇒ : ∀ {n} {e : Tm n} {e′} → ¬ WHNF e → e ⇒ e′ → e CBN.⇒ e′
cbn←no₁-⇒ ¬p (lam r)        = lam ↯ ¬p
cbn←no₁-⇒ ¬p applam         = CBN.applam
cbn←no₁-⇒ ¬p (app₁₋ ¬p₁ r₁) = CBN.app₁ (cbn←no₁-⇒ ¬p₁ r₁)
cbn←no₁-⇒ ¬p (app₁₊ p₁ r₁)  = whnf (app p₁) ↯ ¬p
cbn←no₁-⇒ ¬p (app₂ p₁ r₂)   = whnf (app (naxnf←nanf p₁)) ↯ ¬p

no₁←no₂-⇒ : ∀ {n} {e : Tm n} {e′} → e NO₂.⇒ e′ → e ⇒ e′
no₁←no₂-⇒ (NO₂.lam₋ ¬p r)       = lam (no₁←cbn-⇒ r)
no₁←no₂-⇒ (NO₂.lam₊ p r)        = lam (no₁←no₂-⇒ r)
no₁←no₂-⇒ (NO₂.app₁₊ p₁ r₁)     = app₁₊ p₁ (no₁←no₂-⇒ r₁)
no₁←no₂-⇒ (NO₂.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (no₁←cbn-⇒ r₂)
no₁←no₂-⇒ (NO₂.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (no₁←no₂-⇒ r₂)

no₂←no₁-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → e NO₂.⇒ e′
no₂←no₁-⇒ lam             (lam r)        with whnf? _
... | no ¬p                                = NO₂.lam₋ ¬p (cbn←no₁-⇒ ¬p r)
... | yes p                                = NO₂.lam₊ p (no₂←no₁-⇒ p r)
no₂←no₁-⇒ (whnf var)      ()
no₂←no₁-⇒ (whnf (app ())) applam
no₂←no₁-⇒ (whnf (app p₁)) (app₁₋ ¬p₁ r₁) = whnf p₁ ↯ ¬p₁
no₂←no₁-⇒ (whnf (app _))  (app₁₊ p₁ r₁)  = NO₂.app₁₊ p₁ (no₂←no₁-⇒ (whnf p₁) r₁)
no₂←no₁-⇒ (whnf (app _))  (app₂ p₁ r₂)   with whnf? _
... | no ¬p₂                               = NO₂.app₂₋ p₁ ¬p₂ (cbn←no₁-⇒ ¬p₂ r₂)
... | yes p₂                               = NO₂.app₂₊ p₁ p₂ (no₂←no₁-⇒ p₂ r₂)

cbn|no₂←no₁-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → (e CBN.⇒ e′) ⊎ (e NO₂.⇒ e′)
cbn|no₂←no₁-⇒ (lam r)        with whnf? _
... | no ¬p                    = inj₂ (NO₂.lam₋ ¬p (cbn←no₁-⇒ ¬p r))
... | yes p                    = inj₂ (NO₂.lam₊ p (no₂←no₁-⇒ p r))
cbn|no₂←no₁-⇒ applam         = inj₁ CBN.applam
cbn|no₂←no₁-⇒ (app₁₋ ¬p₁ r₁) = inj₁ (CBN.app₁ (cbn←no₁-⇒ ¬p₁ r₁))
cbn|no₂←no₁-⇒ (app₁₊ p₁ r₁)  = inj₂ (NO₂.app₁₊ p₁ (no₂←no₁-⇒ (whnf p₁) r₁))
cbn|no₂←no₁-⇒ (app₂ p₁ r₂)   with whnf? _
... | no ¬p₂                   = inj₂ (NO₂.app₂₋ p₁ ¬p₂ (cbn←no₁-⇒ ¬p₂ r₂))
... | yes p₂                   = inj₂ (NO₂.app₂₊ p₁ p₂ (no₂←no₁-⇒ p₂ r₂))


---------------------------------------------------------------------------------------------------------------
--
-- More extras for BS-NO₁

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* = applam ◅ ε

cbn-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS-CBN.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
cbn-app₁* = map cbn-app₁

app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁₊* p₁ ε          = ε
app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

no₂←no₁-⇒* : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒* e′ → e SS-NO₂.⇒* e′
no₂←no₁-⇒* p ε        = ε
no₂←no₁-⇒* p (r ◅ rs) = no₂←no₁-⇒ p r ◅ no₂←no₁-⇒* (SS-NO₂.whnf-⇒ (no₂←no₁-⇒ p r)) rs

cbn|no₂←no₁-⇒* : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ →
                   (∃ λ e″ → e SS-CBN.⇒* e″ × WHNF e″ × e″ SS-NO₂.⇒* e′)
cbn|no₂←no₁-⇒* ε        p = _ , ε , whnf←nf p , ε
cbn|no₂←no₁-⇒* (r ◅ rs) p with cbn|no₂←no₁-⇒ r
... | inj₂ r′               = _ , ε , SS-NO₂.rev-whnf-⇒ r′ , r′ ◅ no₂←no₁-⇒* (SS-NO₂.whnf-⇒ r′) rs
... | inj₁ r′               with cbn|no₂←no₁-⇒* rs p
... | _ , rs′ , p′ , rs″    = _ , r′ ◅ rs′ , p′ , rs″


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₁ implies SS-NO

no←no₁ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → e SS-NO.⇒ e′
no←no₁ (lam r)        = SS-NO.lam (no←no₁ r)
no←no₁ applam         = SS-NO.applam
no←no₁ (app₁₋ ¬p₁ r₁) = SS-NO.app₁₋ ¬p₁ (no←no₁ r₁)
no←no₁ (app₁₊ p₁ r₁)  = SS-NO.app₁₊ p₁ (no←no₁ r₁)
no←no₁ (app₂ p₁ r₂)   = SS-NO.app₂ p₁ (no←no₁ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO implies SS-NO₁

no₁←no : ∀ {n} {e : Tm n} {e′} → e SS-NO.⇒ e′ → e ⇒ e′
no₁←no (SS-NO.lam r)      = lam (no₁←no r)
no₁←no SS-NO.applam       = applam
no₁←no (SS-NO.app₁ q₁ r₁) = app₁ q₁ (no₁←no r₁)
no₁←no (SS-NO.app₂ p₁ r₂) = app₂ p₁ (no₁←no r₂)


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₁ and SS-NO coincide

no₁↔no : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ ↔ e SS-NO.⇒ e′
no₁↔no = no←no₁ , no₁←no


---------------------------------------------------------------------------------------------------------------
