---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HNO₂

module A201903.4-8-1-Properties-SmallStep-HNO₂ where

open import A201903.2-2-Semantics-SmallStep
open HNO₂ public
import A201903.4-6-Properties-SmallStep-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-HS-reducible, SS-HNO₂-reducible, or NF

data RF? {n} : Pred₀ (Tm n) where
  hs-yes : ∀ {e} → HS.RF e → RF? e
  yes    : ∀ {e} → HNF e → RF e → RF? e
  no     : ∀ {e} → NF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? e           with HS.rf? e
...             | HS.yes (_ , r)         = hs-yes (_ , r)
rf? (var s x)   | HS.no _                = no (nf var)
rf? (lam s e)   | HS.no (lam p)          with rf? e
... | hs-yes (_ , r)                     = hs-yes (_ , HS.lam r)
... | yes p′ (_ , r)                     = yes (lam p) (_ , lam p r)
... | no p′                              = no (lam p′)
rf? (lam s e)   | HS.no (hnf ())
rf? (app e₁ e₂) | HS.no (hnf (app p₁))   with rf? e₁ | rf? e₂
... | hs-yes (_ , r₁)  | _               = hs-yes (_ , HS.app₁ r₁)
... | yes p₁′ (_ , r₁) | _               = yes (hnf (app p₁)) (_ , app₁ p₁ r₁)
... | no (lam p₁′)     | _               = case p₁ of λ ()
... | no (nf p₁′)      | hs-yes (_ , r₂) = yes (hnf (app p₁))
                                               (_ , hs-app₂ p₁′ (λ p₂′ → r₂ ↯ HS.nrf←hnf p₂′) r₂)
... | no (nf p₁′)      | yes p₂ (_ , r₂) = yes (hnf (app p₁)) (_ , app₂ p₁′ p₂ r₂)
... | no (nf p₁′)      | no p₂           = no (nf (app p₁′ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ does not reduce SS-HS-reducible terms, or NF

hs-rf|nf←nrf : ∀ {n} {e : Tm n} → NRF e → HS.RF e ⊎ NF e
hs-rf|nf←nrf p      with rf? _
... | hs-yes (_ , r) = inj₁ (_ , r)
... | yes p′ (_ , r) = r ↯ p
... | no p′          = inj₂ p′

nrf←hs-rf : ∀ {n} {e : Tm n} → HS.RF e → NRF e
nrf←hs-rf (_ , r) = λ { (lam p r′)          → case r of
                           λ { (HS.lam r″)     → r″ ↯ HS.nrf←hnf p }
                       ; (app₁ p₁ r₁)        → case r of
                           λ { (HS.applam p₁′) → case p₁ of λ ()
                             ; (HS.app₁ r₁′)   → r₁′ ↯ HS.nrf←naxnf p₁ }
                       ; (hs-app₂ p₁ ¬p₂ r₂) → case r of
                           λ { (HS.applam p₁′) → case p₁ of λ ()
                             ; (HS.app₁ r₁′)   → r₁′ ↯ HS.nrf←naxnf (naxnf←nanf p₁) }
                       ; (app₂ p₁ p₂ r₂)     → case r of
                           λ { (HS.applam p₁′) → case p₁ of λ ()
                             ; (HS.app₁ r₁′)   → r₁′ ↯ HS.nrf←naxnf (naxnf←nanf p₁) } }

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam p′ r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (app₁ p₁′ r₁)        → r₁ ↯ nrf←nanf p₁
                            ; (hs-app₂ p₁′ ¬p₂ r₂) → r₂ ↯ HS.nrf←hnf (hnf←nf p₂)
                            ; (app₂ p₁′ p₂′ r₂)    → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ is unique

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _} ()                  ()
uniq-⇒ {e = lam _ _} (lam p r)           (lam p′ r′)            = lam & uniq-hnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)        (app₁ p₁′ r₁′)         = app₁ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)        (hs-app₂ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₁ p₁ r₁)        (app₂ p₁′ p₂′ r₂′)     = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (hs-app₂ p₁ ¬p₂ r₂) (app₁ p₁′ r₁′)         = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (hs-app₂ p₁ ¬p₂ r₂) (hs-app₂ p₁′ ¬p₂′ r₂′) = hs-app₂ & uniq-nanf p₁ p₁′
                                                                           ⊗ uniq-¬hnf ¬p₂ ¬p₂′
                                                                           ⊗ HS.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app _ _} (hs-app₂ p₁ ¬p₂ r₂) (app₂ p₁′ p₂′ r₂′)     = p₂′ ↯ ¬p₂
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)     (app₁ p₁′ r₁′)         = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)     (hs-app₂ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
uniq-⇒ {e = app _ _} (app₂ p₁ p₂ r₂)     (app₂ p₁′ p₂′ r₂′)     = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-hnf p₂ p₂′
                                                                        ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam p r)           (lam p′ r′)            = lam & refl ⊗ det-⇒ r r′
det-⇒ (app₁ p₁ r₁)        (app₁ p₁′ r₁′)         = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁)        (hs-app₂ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₁ p₁ r₁)        (app₂ p₁′ p₂′ r₂′)     = r₁ ↯ nrf←nanf p₁′
det-⇒ (hs-app₂ p₁ ¬p₂ r₂) (app₁ p₁′ r₁′)         = r₁′ ↯ nrf←nanf p₁
det-⇒ (hs-app₂ p₁ ¬p₂ r₂) (hs-app₂ p₁′ ¬p₂′ r₂′) = app & refl ⊗ HS.det-⇒ r₂ r₂′
det-⇒ (hs-app₂ p₁ ¬p₂ r₂) (app₂ p₁′ p₂′ r₂′)     = p₂′ ↯ ¬p₂
det-⇒ (app₂ p₁ p₂ r₂)     (app₁ p₁′ r₁′)         = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ p₂ r₂)     (hs-app₂ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂ p₁ p₂ r₂)     (app₂ p₁′ p₂′ r₂′)     = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO₂ preserves HNF and goes from HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁ p₁ r₁)         = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (hs-app₂ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂ p₁′ p₂ r₂)     = app p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → HNF e′
hnf-⇒ (lam p r)           = lam (hnf-⇒ r)
hnf-⇒ (app₁ p₁ r₁)        = hnf (app (naxnf-⇒ p₁ r₁))
hnf-⇒ (hs-app₂ p₁ ¬p₂ r₂) = hnf (app (naxnf←nanf p₁))
hnf-⇒ (app₂ p₁ ¬p₂ r₂)    = hnf (app (naxnf←nanf p₁))

rev-hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → HNF e
rev-hnf-⇒ (lam p r)           = lam p
rev-hnf-⇒ (app₁ p₁ r₁)        = hnf (app p₁)
rev-hnf-⇒ (hs-app₂ p₁ ¬p₂ r₂) = hnf (app (naxnf←nanf p₁))
rev-hnf-⇒ (app₂ p₁ p₂ r₂)     = hnf (app (naxnf←nanf p₁))


---------------------------------------------------------------------------------------------------------------
