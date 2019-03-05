---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-NO where

open import Semantics-SmallStep
open NO public
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-SmallStep-NO₂ as SS-NO₂


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam)      → case p₁ of λ ()
                            ; (_ , app₁ p₁′ r₁) → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic′ _⇒_
det-⇒ (lam r)      (lam r′)       = lam & det-⇒ r r′
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ applam       (app₂ () r₂′)
det-⇒ (app₁ () r₁) applam
det-⇒ (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁) (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂) applam
det-⇒ (app₂ p₁ r₂) (app₁ p₁′ r₁′) = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO preserves NF and WHNF

mutual
  nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
  nf-⇒ (lam p) (lam r) = lam (nf-⇒ p r)
  nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)

  nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
  nanf-⇒ var         ()
  nanf-⇒ (app () p₂) applam
  nanf-⇒ (app p₁ p₂) (app₁ p₁′ r₁) = app (nanf-⇒ p₁ r₁) p₂
  nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = app p₁′ (nf-⇒ p₂ r₂)

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ p₁′ r₁) = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂ p₁′ r₂) = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      (lam r) = lam
whnf-⇒ (whnf p) r       = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
--
-- Extras for BS-NO

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁ app applam
cbn-app₁ (CBN.app₁ r₁) = app₁ app (cbn-app₁ r₁)

no←cbn-⇒ : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
no←cbn-⇒ CBN.applam    = applam
no←cbn-⇒ (CBN.app₁ r₁) = cbn-app₁ r₁

cbn←no-⇒ : ∀ {n} {e : Tm n} {e′} → ¬ WHNF e → e ⇒ e′ → e CBN.⇒ e′
cbn←no-⇒ ¬p (lam r)      = lam ↯ ¬p
cbn←no-⇒ ¬p applam       = CBN.applam
cbn←no-⇒ ¬p (app₁ p₁ r₁) with whnf? _
... | no ¬p₁′              = CBN.app₁ (cbn←no-⇒ ¬p₁′ r₁)
... | yes p₁′              = whnf (app (naxnf←whnf p₁′ p₁)) ↯ ¬p
cbn←no-⇒ ¬p (app₂ p₁ r₂) = whnf (app (naxnf←nanf p₁)) ↯ ¬p

no←no₂-⇒ : ∀ {n} {e : Tm n} {e′} → e NO₂.⇒ e′ → e ⇒ e′
no←no₂-⇒ (NO₂.lam₋ ¬p r)       = lam (no←cbn-⇒ r)
no←no₂-⇒ (NO₂.lam₊ p r)        = lam (no←no₂-⇒ r)
no←no₂-⇒ (NO₂.app₁₊ p₁ r₁)     = app₁ (na←naxnf p₁) (no←no₂-⇒ r₁)
no←no₂-⇒ (NO₂.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (no←cbn-⇒ r₂)
no←no₂-⇒ (NO₂.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (no←no₂-⇒ r₂)

no₂←no-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → e NO₂.⇒ e′
no₂←no-⇒ lam             (lam r)       with whnf? _
... | no ¬p                              = NO₂.lam₋ ¬p (cbn←no-⇒ ¬p r)
... | yes p                              = NO₂.lam₊ p (no₂←no-⇒ p r)
no₂←no-⇒ (whnf var)      ()
no₂←no-⇒ (whnf (app ())) applam
no₂←no-⇒ (whnf (app p₁)) (app₁ p₁′ r₁) = NO₂.app₁₊ p₁ (no₂←no-⇒ (whnf p₁) r₁)
no₂←no-⇒ (whnf (app _))  (app₂ p₁ r₂)  with whnf? _
... | no ¬p₂                             = NO₂.app₂₋ p₁ ¬p₂ (cbn←no-⇒ ¬p₂ r₂)
... | yes p₂                             = NO₂.app₂₊ p₁ p₂ (no₂←no-⇒ p₂ r₂)

cbn|no₂←no-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → (e CBN.⇒ e′) ⊎ (e NO₂.⇒ e′)
cbn|no₂←no-⇒ (lam r)      with whnf? _
... | no ¬p                 = inj₂ (NO₂.lam₋ ¬p (cbn←no-⇒ ¬p r))
... | yes p                 = inj₂ (NO₂.lam₊ p (no₂←no-⇒ p r))
cbn|no₂←no-⇒ applam       = inj₁ CBN.applam
cbn|no₂←no-⇒ (app₁ p₁ r₁) with whnf? _
... | no ¬p₁′               = inj₁ (CBN.app₁ (cbn←no-⇒ ¬p₁′ r₁))
... | yes p₁′               = inj₂ (NO₂.app₁₊ (naxnf←whnf p₁′ p₁) (no₂←no-⇒ p₁′ r₁))
cbn|no₂←no-⇒ (app₂ p₁ r₂) with whnf? _
... | no ¬p₂                = inj₂ (NO₂.app₂₋ p₁ ¬p₂ (cbn←no-⇒ ¬p₂ r₂))
... | yes p₂                = inj₂ (NO₂.app₂₊ p₁ p₂ (no₂←no-⇒ p₂ r₂))


---------------------------------------------------------------------------------------------------------------
--
-- Extras for SS-NO₁

app₁₋ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → ¬ WHNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₋ ¬p₁ applam       = app₁ app applam
app₁₋ ¬p₁ (app₁ q₁ r₁) = app₁ app (app₁ q₁ r₁)
app₁₋ ¬p₁ (app₂ p₁ r₂) = app₁ app (app₂ p₁ r₂)
app₁₋ ¬p₁ (lam r)      = lam ↯ ¬p₁

app₁₊ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₊ var      r₁ = app₁ var r₁
app₁₊ (app p₁) r₁ = app₁ app r₁


---------------------------------------------------------------------------------------------------------------
--
-- More extras for BS-NO

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

no₂←no-⇒* : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒* e′ → e SS-NO₂.⇒* e′
no₂←no-⇒* p ε        = ε
no₂←no-⇒* p (r ◅ rs) = no₂←no-⇒ p r ◅ no₂←no-⇒* (SS-NO₂.whnf-⇒ (no₂←no-⇒ p r)) rs

cbn|no₂←no-⇒* : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ →
                  (∃ λ e″ → e SS-CBN.⇒* e″ × WHNF e″ × e″ SS-NO₂.⇒* e′)
cbn|no₂←no-⇒* ε        p = _ , ε , whnf←nf p , ε
cbn|no₂←no-⇒* (r ◅ rs) p with cbn|no₂←no-⇒ r
... | inj₂ r′              = _ , ε , SS-NO₂.rev-whnf-⇒ r′ , r′ ◅ no₂←no-⇒* (SS-NO₂.whnf-⇒ r′) rs
... | inj₁ r′              with cbn|no₂←no-⇒* rs p
... | _ , rs′ , p′ , rs″   = _ , r′ ◅ rs′ , p′ , rs″


---------------------------------------------------------------------------------------------------------------
