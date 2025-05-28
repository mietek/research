{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO₂

module A201903.4-2-1-Properties-SmallStep-NO₂ where

open import A201903.2-2-Semantics-SmallStep
open NO₂ public
import A201903.4-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBN-reducible, SS-NO₂-reducible, or NF

data RF? {n} : Pred₀ (Tm n) where
  cbn-yës : ∀ {e} → CBN.RF e → RF? e
  yës     : ∀ {e} → WHNF e → RF e → RF? e
  nö      : ∀ {e} → NF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? e           with CBN.rf? e
...             | CBN.yës (_ , r)         = cbn-yës (_ , r)
rf? (var s x)   | CBN.nö _                = nö (nf var)
rf? (lam s e)   | CBN.nö _                with rf? e
... | cbn-yës (_ , r)                     = yës lam (_ , cbn-lam (λ p′ → r ↯ CBN.nrf←whnf p′) r)
... | yës p (_ , r)                       = yës lam (_ , lam p r)
... | nö p                                = nö (lam p)
rf? (app e₁ e₂) | CBN.nö (whnf (app p₁))  with rf? e₁ | rf? e₂
... | cbn-yës (_ , r₁) | _                = cbn-yës (_ , CBN.app₁ r₁)
... | yës p₁′ (_ , r₁) | _                = yës (whnf (app p₁)) (_ , app₁ p₁ r₁)
... | nö (lam p₁′)     | _                = cbn-yës (_ , CBN.applam)
... | nö (nf p₁′)      | cbn-yës (_ , r₂) = yës (whnf (app p₁))
                                                (_ , cbn-app₂ p₁′ (λ p₂′ → r₂ ↯ CBN.nrf←whnf p₂′) r₂)
... | nö (nf p₁′)      | yës p₂ (_ , r₂)  = yës (whnf (app p₁)) (_ , app₂ p₁′ p₂ r₂)
... | nö (nf p₁′)      | nö p₂            = nö (nf (app p₁′ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ does not reduce SS-CBN-reducible terms, or NF

cbn-rf|nf←nrf : ∀ {n} {e : Tm n} → NRF e → CBN.RF e ⊎ NF e
cbn-rf|nf←nrf p      with rf? _
... | cbn-yës (_ , r) = inj₁ (_ , r)
... | yës p′ (_ , r)  = r ↯ p
... | nö p′           = inj₂ p′

nrf←cbn-rf : ∀ {n} {e : Tm n} → CBN.RF e → NRF e
nrf←cbn-rf (_ , r) = λ { (cbn-lam ¬p r′)      → case r of λ ()
                        ; (lam p r′)           → case r of λ ()
                        ; (app₁ p₁ r₁)         → case r of
                            λ { CBN.applam       → case p₁ of λ ()
                              ; (CBN.app₁ r₁′)   → r₁′ ↯ CBN.nrf←naxnf p₁ }
                        ; (cbn-app₂ p₁ ¬p₂ r₂) → case r of
                            λ { CBN.applam       → case p₁ of λ ()
                              ; (CBN.app₁ r₁′)   → r₁′ ↯ CBN.nrf←naxnf (naxnf←nanf p₁) }
                        ; (app₂ p₁ p₂ r₂)      → case r of
                            λ { CBN.applam       → case p₁ of λ ()
                              ; (CBN.app₁ r₁′)   → r₁′ ↯ CBN.nrf←naxnf (naxnf←nanf p₁) } }

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (cbn-lam ¬p r) → whnf←nf p ↯ ¬p
                      ; (lam p′ r)     → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (app₁ p₁′ r₁)         → r₁ ↯ nrf←nanf p₁
                            ; (cbn-app₂ p₁′ ¬p₂ r₂) → r₂ ↯ CBN.nrf←whnf (whnf←nf p₂)
                            ; (app₂ p₁′ p₂′ r₂)     → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is unique

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _} ()                   ()
uniq-⇒ {e = lam _ _} (cbn-lam ¬p r)       (cbn-lam ¬p′ r′)        = cbn-lam & uniq-¬whnf ¬p ¬p′
                                                                             ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _ _} (cbn-lam ¬p r)       (lam p′ r′)             = p′ ↯ ¬p
uniq-⇒ {e = lam _ _} (lam p r)            (cbn-lam ¬p′ r′)        = p ↯ ¬p′
uniq-⇒ {e = lam _ _} (lam p r)            (lam p′ r′)             = lam & uniq-whnf p p′
                                                                         ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)         (app₁ p₁′ r₁′)          = app₁ & uniq-naxnf p₁ p₁′
                                                                          ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)         (cbn-app₂ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)         (app₂ p₁′ p₂′ r₂′)      = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (cbn-app₂ p₁ ¬p₂ r₂) (app₁ p₁′ r₁′)          = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (cbn-app₂ p₁ ¬p₂ r₂) (cbn-app₂ p₁′ ¬p₂′ r₂′) = cbn-app₂ & uniq-nanf p₁ p₁′
                                                                              ⊗ uniq-¬whnf ¬p₂ ¬p₂′
                                                                              ⊗ CBN.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app _ _} (cbn-app₂ p₁ ¬p₂ r₂) (app₂ p₁′ p₂′ r₂′)      = p₂′ ↯ ¬p₂
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)      (app₁ p₁′ r₁′)          = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)      (cbn-app₂ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)      (app₂ p₁′ p₂′ r₂′)      = app₂ & uniq-nanf p₁ p₁′
                                                                          ⊗ uniq-whnf p₂ p₂′
                                                                          ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (cbn-lam ¬p r)       (cbn-lam ¬p′ r′)        = lam & refl ⊗ CBN.det-⇒ r r′
det-⇒ (cbn-lam ¬p r)       (lam p′ r′)             = p′ ↯ ¬p
det-⇒ (lam p r)            (cbn-lam ¬p′ r′)        = p ↯ ¬p′
det-⇒ (lam p r)            (lam p′ r′)             = lam & refl ⊗ det-⇒ r r′
det-⇒ (app₁ p₁ r₁)         (app₁ p₁′ r₁′)          = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁)         (cbn-app₂ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₁ p₁ r₁)         (app₂ p₁′ p₂′ r₂′)      = r₁ ↯ nrf←nanf p₁′
det-⇒ (cbn-app₂ p₁ ¬p₂ r₂) (app₁ p₁′ r₁′)          = r₁′ ↯ nrf←nanf p₁
det-⇒ (cbn-app₂ p₁ ¬p₂ r₂) (cbn-app₂ p₁′ ¬p₂′ r₂′) = app & refl ⊗ CBN.det-⇒ r₂ r₂′
det-⇒ (cbn-app₂ p₁ ¬p₂ r₂) (app₂ p₁′ p₂′ r₂′)      = p₂′ ↯ ¬p₂
det-⇒ (app₂ p₁ p₂ r₂)      (app₁ p₁′ r₁′)          = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ p₂ r₂)      (cbn-app₂ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂ p₁ p₂ r₂)      (app₂ p₁′ p₂′ r₂′)      = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁ p₁ r₁)          = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (cbn-app₂ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂ p₁′ p₂ r₂)      = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (cbn-lam ¬p r)       = lam
whnf-⇒ (lam p r)            = lam
whnf-⇒ (app₁ p₁ r₁)         = whnf (app (naxnf-⇒ p₁ r₁))
whnf-⇒ (cbn-app₂ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
whnf-⇒ (app₂ p₁ ¬p₂ r₂)     = whnf (app (naxnf←nanf p₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (cbn-lam ¬p r)       = lam
rev-whnf-⇒ (lam p r)            = lam
rev-whnf-⇒ (app₁ p₁ r₁)         = whnf (app p₁)
rev-whnf-⇒ (cbn-app₂ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
rev-whnf-⇒ (app₂ p₁ p₂ r₂)      = whnf (app (naxnf←nanf p₁))


---------------------------------------------------------------------------------------------------------------
