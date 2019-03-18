---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H₂

module 4-7-2-Properties-SmallStep-H₂ where

open import 2-2-Semantics-SmallStep
open H₂ public
import 4-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBN-reducible, SS-H₂-reducible, or HNF

data RF? {n} : Pred₀ (Tm n) where
  cbn-yes : ∀ {e} → CBN.RF e → RF? e
  yes     : ∀ {e} → WHNF e → RF e → RF? e
  no      : ∀ {e} → HNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? e           with CBN.rf? e
...             | CBN.yes (_ , r)        = cbn-yes (_ , r)
rf? (var x)     | CBN.no _               = no (hnf var)
rf? (lam e)     | CBN.no _               with rf? e
... | cbn-yes (_ , r)                    = yes lam (_ , lam₋ (λ p′ → r ↯ CBN.nrf←whnf p′) r)
... | yes p (_ , r)                      = yes lam (_ , lam₊ p r)
... | no p                               = no (lam p)
rf? (app e₁ e₂) | CBN.no (whnf (app p₁)) with rf? e₁
... | cbn-yes (_ , r₁)                   = cbn-yes (_ , CBN.app₁ r₁)
... | yes p₁′ (_ , r₁)                   = no (hnf (app p₁))
... | no p₁′                             = no (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ does not reduce SS-CBN-reducible terms, or HNF

cbn-rf|hnf←nrf : ∀ {n} {e : Tm n} → NRF e → CBN.RF e ⊎ HNF e
cbn-rf|hnf←nrf p      with rf? _
... | cbn-yes (_ , r) = inj₁ (_ , r)
... | yes p′ (_ , r)  = r ↯ p
... | no p′           = inj₂ p′

nrf←cbn-rf : ∀ {n} {e : Tm n} → CBN.RF e → NRF e
nrf←cbn-rf (_ , r) = λ { (lam₋ ¬p r′)      → case r of λ ()
                        ; (lam₊ p r′)       → case r of λ ()
                        ; (app₁₊ p₁ r₁)     → case r of
                            λ { CBN.applam     → case p₁ of λ ()
                              ; (CBN.app₁ r₁′) → r₁′ ↯ CBN.nrf←naxnf p₁ } }

mutual
  nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
  nrf←hnf (lam p) = λ { (lam₋ ¬p r) → whnf←hnf p ↯ ¬p
                       ; (lam₊ p′ r) → r ↯ nrf←hnf p }
  nrf←hnf (hnf p) = nrf←naxnf p

  nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
  nrf←naxnf var      = λ ()
  nrf←naxnf (app p₁) = λ { (app₁₊ p₁′ r₁) → r₁ ↯ nrf←naxnf p₁ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is unique

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}   ()            ()
uniq-⇒ {e = lam _}   (lam₋ ¬p r)   (lam₋ ¬p′ r′)   = lam₋ & uniq-¬whnf ¬p ¬p′  ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _}   (lam₋ ¬p r)   (lam₊ p′ r′)    = p′ ↯ ¬p
uniq-⇒ {e = lam _}   (lam₊ p r)    (lam₋ ¬p′ r′)   = p ↯ ¬p′
uniq-⇒ {e = lam _}   (lam₊ p r)    (lam₊ p′ r′)    = lam₊ & uniq-whnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁) (app₁₊ p₁′ r₁′) = app₁₊ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam₋ ¬p r)   (lam₋ ¬p′ r′)   = lam & CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)   (lam₊ p′ r′)    = p′ ↯ ¬p
det-⇒ (lam₊ p r)    (lam₋ ¬p′ r′)   = p ↯ ¬p′
det-⇒ (lam₊ p r)    (lam₊ p′ r′)    = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁) (app₁₊ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-H₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (lam₋ ¬p r)   = lam
whnf-⇒ (lam₊ p r)    = lam
whnf-⇒ (app₁₊ p₁ r₁) = whnf (app (naxnf-⇒ p₁ r₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (lam₋ ¬p r)   = lam
rev-whnf-⇒ (lam₊ p r)    = lam
rev-whnf-⇒ (app₁₊ p₁ r₁) = whnf (app p₁)


---------------------------------------------------------------------------------------------------------------
