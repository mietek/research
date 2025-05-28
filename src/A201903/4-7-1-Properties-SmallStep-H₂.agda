{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H₂

module A201903.4-7-1-Properties-SmallStep-H₂ where

open import A201903.2-2-Semantics-SmallStep
open H₂ public
import A201903.4-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBN-reducible, SS-H₂-reducible, or HNF

data RF? {n} : Pred₀ (Tm n) where
  cbn-yës : ∀ {e} → CBN.RF e → RF? e
  yës     : ∀ {e} → WHNF e → RF e → RF? e
  nö      : ∀ {e} → HNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? e           with CBN.rf? e
...             | CBN.yës (_ , r)        = cbn-yës (_ , r)
rf? (var s x)   | CBN.nö _               = nö (hnf var)
rf? (lam s e)   | CBN.nö _               with rf? e
... | cbn-yës (_ , r)                    = yës lam (_ , cbn-lam (λ p′ → r ↯ CBN.nrf←whnf p′) r)
... | yës p (_ , r)                      = yës lam (_ , lam p r)
... | nö p                               = nö (lam p)
rf? (app e₁ e₂) | CBN.nö (whnf (app p₁)) with rf? e₁
... | cbn-yës (_ , r₁)                   = cbn-yës (_ , CBN.app₁ r₁)
... | yës p₁′ (_ , r₁)                   = nö (hnf (app p₁))
... | nö p₁′                             = nö (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ does not reduce SS-CBN-reducible terms, or HNF

cbn-rf|hnf←nrf : ∀ {n} {e : Tm n} → NRF e → CBN.RF e ⊎ HNF e
cbn-rf|hnf←nrf p      with rf? _
... | cbn-yës (_ , r) = inj₁ (_ , r)
... | yës p′ (_ , r)  = r ↯ p
... | nö p′           = inj₂ p′

nrf←cbn-rf : ∀ {n} {e : Tm n} → CBN.RF e → NRF e
nrf←cbn-rf (_ , r) = λ { (cbn-lam ¬p r′) → case r of λ ()
                        ; (lam p r′)      → case r of λ ()
                        ; (app₁ p₁ r₁)    → case r of
                            λ { CBN.applam     → case p₁ of λ ()
                              ; (CBN.app₁ r₁′) → r₁′ ↯ CBN.nrf←naxnf p₁ } }

mutual
  nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
  nrf←hnf (lam p) = λ { (cbn-lam ¬p r) → whnf←hnf p ↯ ¬p
                       ; (lam p′ r)     → r ↯ nrf←hnf p }
  nrf←hnf (hnf p) = nrf←naxnf p

  nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
  nrf←naxnf var      = λ ()
  nrf←naxnf (app p₁) = λ { (app₁ p₁′ r₁) → r₁ ↯ nrf←naxnf p₁ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is unique

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _} ()             ()
uniq-⇒ {e = lam _ _} (cbn-lam ¬p r) (cbn-lam ¬p′ r′) = cbn-lam & uniq-¬whnf ¬p ¬p′ ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _ _} (cbn-lam ¬p r) (lam p′ r′)      = p′ ↯ ¬p
uniq-⇒ {e = lam _ _} (lam p r)      (cbn-lam ¬p′ r′) = p ↯ ¬p′
uniq-⇒ {e = lam _ _} (lam p r)      (lam p′ r′)      = lam & uniq-whnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)   (app₁ p₁′ r₁′)   = app₁ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (cbn-lam ¬p r) (cbn-lam ¬p′ r′) = lam & refl ⊗ CBN.det-⇒ r r′
det-⇒ (cbn-lam ¬p r) (lam p′ r′)      = p′ ↯ ¬p
det-⇒ (lam p r)      (cbn-lam ¬p′ r′) = p ↯ ¬p′
det-⇒ (lam p r)      (lam p′ r′)      = lam & refl ⊗ det-⇒ r r′
det-⇒ (app₁ p₁ r₁)   (app₁ p₁′ r₁′)   = app & det-⇒ r₁ r₁′ ⊗ refl

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁ p₁ r₁) = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (cbn-lam ¬p r) = lam
whnf-⇒ (lam p r)      = lam
whnf-⇒ (app₁ p₁ r₁)   = whnf (app (naxnf-⇒ p₁ r₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (cbn-lam ¬p r) = lam
rev-whnf-⇒ (lam p r)      = lam
rev-whnf-⇒ (app₁ p₁ r₁)   = whnf (app p₁)


---------------------------------------------------------------------------------------------------------------
