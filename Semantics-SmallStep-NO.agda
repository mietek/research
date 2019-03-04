---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-NO where

open import Semantics-SmallStep
open NO public
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-SmallStep-NO₊ as SS-NO₊


---------------------------------------------------------------------------------------------------------------

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

det-⇒ : Deterministic′ _⇒_
det-⇒ applam         applam           = refl
det-⇒ applam         (app₁₋ ¬p₁′ r₁′) = lam ↯ ¬p₁′
det-⇒ applam         (app₁₊ () r₁′)
det-⇒ applam         (app₂ () r₂′)
det-⇒ (app₁₋ ¬p₁ r₁) applam           = lam ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁) (app₁₋ ¬p₁′ r′)  = app & det-⇒ r₁ r′ ⊗ refl
det-⇒ (app₁₋ ¬p₁ r₁) (app₁₊ p₁′ r′)   = whnf p₁′ ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁) (app₂ p₁′ r′)    = whnf←nf (nf p₁′) ↯ ¬p₁
det-⇒ (app₁₊ () r₁)  applam
det-⇒ (app₁₊ p₁ r₁)  (app₁₋ ¬p₁′ r₁′) = whnf p₁ ↯ ¬p₁′
det-⇒ (app₁₊ p₁ r₁)  (app₁₊ p₁′ r₁′)  = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)  (app₂ p₁′ r₂′)   = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂)   applam
det-⇒ (app₂ p₁ r₂)   (app₁₋ ¬p₁′ r₁′) = whnf←nf (nf p₁) ↯ ¬p₁′
det-⇒ (app₂ p₁ r₂)   (app₁₊ p₁′ r₁′)  = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂)   (app₂ p₁′ r₂′)   = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (lam r)        (lam r′)         = lam & det-⇒ r r′


---------------------------------------------------------------------------------------------------------------

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


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public

{-# DISPLAY _*⟨_⟩ _⇒_ i e e′ = e ⇒*⟨ i ⟩ e′ #-}
{-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′ = e ⇒* e′ #-}
{-# DISPLAY _* _⇒_ e e′ = e ⇒* e′ #-}


---------------------------------------------------------------------------------------------------------------

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁₋ (λ { (whnf (app ())) }) applam
cbn-app₁ (CBN.app₁ r₁) with naxnf? _
... | no ¬p₁           = app₁₋ (λ { (whnf p₁) → p₁ ↯ ¬p₁ }) (cbn-app₁ r₁)
... | yes p₁           = app₁₊ p₁ (cbn-app₁ r₁)

no←cbn-⇒ : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
no←cbn-⇒ CBN.applam    = applam
no←cbn-⇒ (CBN.app₁ r₁) = cbn-app₁ r₁

cbn←no-⇒ : ∀ {n} {e : Tm n} {e′} → ¬ WHNF e → e ⇒ e′ → e CBN.⇒ e′
cbn←no-⇒ ¬p applam         = CBN.applam
cbn←no-⇒ ¬p (app₁₋ ¬p₁ r₁) = CBN.app₁ (cbn←no-⇒ ¬p₁ r₁)
cbn←no-⇒ ¬p (app₁₊ p₁ r₁)  = whnf (app p₁) ↯ ¬p
cbn←no-⇒ ¬p (app₂ p₁ r₂)   = whnf (app (naxnf←nanf p₁)) ↯ ¬p
cbn←no-⇒ ¬p (lam r)        = lam ↯ ¬p

no←no₊-⇒ : ∀ {n} {e : Tm n} {e′} → e NO₊.⇒ e′ → e ⇒ e′
no←no₊-⇒ (NO₊.app₁₊ p₁ r₁)     = app₁₊ p₁ (no←no₊-⇒ r₁)
no←no₊-⇒ (NO₊.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (no←cbn-⇒ r₂)
no←no₊-⇒ (NO₊.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (no←no₊-⇒ r₂)
no←no₊-⇒ (NO₊.lam₋ ¬p r)       = lam (no←cbn-⇒ r)
no←no₊-⇒ (NO₊.lam₊ p r)        = lam (no←no₊-⇒ r)

no₊←no-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → e NO₊.⇒ e′
no₊←no-⇒ (whnf var)      ()
no₊←no-⇒ (whnf (app ())) applam
no₊←no-⇒ (whnf (app p₁)) (app₁₋ ¬p₁ r₁) = whnf p₁ ↯ ¬p₁
no₊←no-⇒ (whnf (app _))  (app₁₊ p₁ r₁)  = NO₊.app₁₊ p₁ (no₊←no-⇒ (whnf p₁) r₁)
no₊←no-⇒ (whnf (app _))  (app₂ p₁ r₂)   with whnf? _
... | no ¬p₂                              = NO₊.app₂₋ p₁ ¬p₂ (cbn←no-⇒ ¬p₂ r₂)
... | yes p₂                              = NO₊.app₂₊ p₁ p₂ (no₊←no-⇒ p₂ r₂)
no₊←no-⇒ lam             (lam r)        with whnf? _
... | no ¬p                               = NO₊.lam₋ ¬p (cbn←no-⇒ ¬p r)
... | yes p                               = NO₊.lam₊ p (no₊←no-⇒ p r)

cbn|no₊←no-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → (e CBN.⇒ e′) ⊎ (e NO₊.⇒ e′)
cbn|no₊←no-⇒ applam         = inj₁ CBN.applam
cbn|no₊←no-⇒ (app₁₋ ¬p₁ r₁) = inj₁ (CBN.app₁ (cbn←no-⇒ ¬p₁ r₁))
cbn|no₊←no-⇒ (app₁₊ p₁ r₁)  = inj₂ (NO₊.app₁₊ p₁ (no₊←no-⇒ (whnf p₁) r₁))
cbn|no₊←no-⇒ (app₂ p₁ r₂)   with whnf? _
... | no ¬p₂                  = inj₂ (NO₊.app₂₋ p₁ ¬p₂ (cbn←no-⇒ ¬p₂ r₂))
... | yes p₂                  = inj₂ (NO₊.app₂₊ p₁ p₂ (no₊←no-⇒ p₂ r₂))
cbn|no₊←no-⇒ (lam r)        with whnf? _
... | no ¬p                   = inj₂ (NO₊.lam₋ ¬p (cbn←no-⇒ ¬p r))
... | yes p                   = inj₂ (NO₊.lam₊ p (no₊←no-⇒ p r))


---------------------------------------------------------------------------------------------------------------

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* = applam ◅ ε

cbn-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS-CBN.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
cbn-app₁* = map cbn-app₁

app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁₊* p₁ ε          = ε
app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* p₁ = map (app₂ p₁)

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam

no₊←no-⇒* : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒* e′ → e SS-NO₊.⇒* e′
no₊←no-⇒* p ε        = ε
no₊←no-⇒* p (r ◅ rs) = no₊←no-⇒ p r ◅ no₊←no-⇒* (SS-NO₊.whnf-⇒ (no₊←no-⇒ p r)) rs

cbn|no₊←no-⇒* : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → NF e′ →
                  (∃ λ e″ → e SS-CBN.⇒* e″ × WHNF e″ × e″ SS-NO₊.⇒* e′)
cbn|no₊←no-⇒* ε        p = _ , ε , whnf←nf p , ε
cbn|no₊←no-⇒* (r ◅ rs) p with cbn|no₊←no-⇒ r
... | inj₂ r′              = _ , ε , SS-NO₊.rev-whnf-⇒ r′ , r′ ◅ no₊←no-⇒* (SS-NO₊.whnf-⇒ r′) rs
... | inj₁ r′              with cbn|no₊←no-⇒* rs p
... | _ , rs′ , p′ , rs″   = _ , r′ ◅ rs′ , p′ , rs″


---------------------------------------------------------------------------------------------------------------
