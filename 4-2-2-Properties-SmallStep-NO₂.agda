---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO₂

module 4-2-2-Properties-SmallStep-NO₂ where

open import 2-2-Semantics-SmallStep
open NO₂ public
import 4-1-Properties-SmallStep-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBN reducible, SS-NO₂ reducible, NF, or NANF

data Form : ∀ {n} → Pred₀ (Tm n) where
  cbn-rf : ∀ {n} {e : Tm n} → CBN.RF e → Form e
  rf     : ∀ {n} {e : Tm n} → WHNF e → RF e → Form e
  nanf   : ∀ {n} {e : Tm n} → NANF e → Form e
  nf     : ∀ {n} {e : Tm n} → ¬ NANF e → NF e → Form e

form? : ∀ {n} (e : Tm n) → Form e
form? e               with CBN.form? e
...                   | CBN.rf (_ , r)       = cbn-rf (_ , r)
form? (var x)         | _                    = nanf var
form? (lam e)         | CBN.whnf _ lam       with form? e
... | cbn-rf (_ , r)                         = rf lam (_ , lam₋ (λ p′ → CBN.nrf←whnf p′ r) r)
... | rf p (_ , r)                           = rf lam (_ , lam₊ p r)
... | nanf p                                 = nf (λ ()) (lam (nf p))
... | nf _ p                                 = nf (λ ()) (lam p)
form? (lam e)         | CBN.whnf _ (whnf ())
form? (lam e)         | CBN.naxnf ()
form? (app e₁ e₂)     | CBN.whnf ¬p (whnf p) = p ↯ ¬p
form? (app e₁ e₂)     | CBN.naxnf (app p₁)   with form? e₁ | form? e₂
... | cbn-rf (_ , r₁) | _                    = cbn-rf (_ , CBN.app₁ r₁)
... | rf p₁′ (_ , r₁) | _                    = rf (whnf (app p₁)) (_ , app₁₊ p₁ r₁)
... | nanf p₁′        | cbn-rf (_ , r₂)      = rf (whnf (app p₁))
                                                  (_ , app₂₋ p₁′ (λ p₂′ → r₂ ↯ CBN.nrf←whnf p₂′) r₂)
... | nanf p₁′        | rf p₂ (_ , r₂)       = rf (whnf (app p₁)) (_ , app₂₊ p₁′ p₂ r₂)
... | nanf p₁′        | nanf p₂              = nanf (app p₁′ (nf p₂))
... | nanf p₁′        | nf _ p₂              = nanf (app p₁′ p₂)
... | nf ¬p₁′ p₁′     | _                    = nanf←nf p₁′ (na←naxnf p₁) ↯ ¬p₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ does not reduce NF

nrf←cbn-rf : ∀ {n} {e : Tm n} → CBN.RF e → NRF e
nrf←cbn-rf (_ , r) = λ { (lam₋ ¬p r′)      → case r of λ ()
                        ; (lam₊ p r′)       → case r of λ ()
                        ; (app₁₊ p₁ r₁)     → case r of
                            λ { CBN.applam     → case p₁ of λ ()
                              ; (CBN.app₁ r₁′) → r₁′ ↯ CBN.nrf←naxnf p₁ }
                        ; (app₂₋ p₁ ¬p₂ r₂) → case r of
                            λ { CBN.applam     → case p₁ of λ ()
                              ; (CBN.app₁ r₁′) → r₁′ ↯ CBN.nrf←naxnf (naxnf←nanf p₁) }
                        ; (app₂₊ p₁ p₂ r₂)  → case r of
                            λ { CBN.applam     → case p₁ of λ ()
                              ; (CBN.app₁ r₁′) → r₁′ ↯ CBN.nrf←naxnf (naxnf←nanf p₁) } }

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam₋ ¬p r) → whnf←nf p ↯ ¬p
                      ; (lam₊ p′ r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (app₁₊ p₁′ r₁)     → r₁ ↯ nrf←nanf p₁
                            ; (app₂₋ p₁′ ¬p₂ r₂) → r₂ ↯ CBN.nrf←whnf (whnf←nf p₂)
                            ; (app₂₊ p₁′ p₂′ r₂) → r₂ ↯ nrf←nf p₂ }

cbn-rf|nf←nrf : ∀ {n} {e : Tm n} → NRF e → CBN.RF e ⊎ NF e
cbn-rf|nf←nrf p with form? _
... | cbn-rf (_ , r) = inj₁ (_ , r)
... | rf p′ (_ , r)  = r ↯ p
... | nanf p′        = inj₂ (nf p′)
... | nf _ p′        = inj₂ p′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is unique

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}   ()                ()
uniq-⇒ {e = lam _}   (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam₋ & uniq-¬whnf ¬p ¬p′  ⊗ CBN.uniq-⇒ r r′
uniq-⇒ {e = lam _}   (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
uniq-⇒ {e = lam _}   (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
uniq-⇒ {e = lam _}   (lam₊ p r)        (lam₊ p′ r′)         = lam₊ & uniq-whnf p p′ ⊗ uniq-⇒ r r′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app₁₊ & uniq-naxnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app₂₋ & uniq-nanf p₁ p₁′ ⊗ uniq-¬whnf ¬p₂ ¬p₂′
                                                                     ⊗ CBN.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app _ _} (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
uniq-⇒ {e = app _ _} (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app₂₊ & uniq-nanf p₁ p₁′ ⊗ uniq-whnf p₂ p₂′
                                                                     ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam₋ ¬p r)       (lam₋ ¬p′ r′)        = lam & CBN.det-⇒ r r′
det-⇒ (lam₋ ¬p r)       (lam₊ p′ r′)         = p′ ↯ ¬p
det-⇒ (lam₊ p r)        (lam₋ ¬p′ r′)        = p ↯ ¬p′
det-⇒ (lam₊ p r)        (lam₊ p′ r′)         = lam & det-⇒ r r′
det-⇒ (app₁₊ p₁ r₁)     (app₁₊ p₁′ r₁′)      = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ r₁)     (app₂₋ p₁′ ¬p₂′ r₂′) = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₁₊ p₁ r₁)     (app₂₊ p₁′ p₂′ r₂′)  = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ r₁′)      = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ CBN.det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ p₂′ r₂′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₁₊ p₁′ r₁′)      = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₂₊ p₁ p₂ r₂)  (app₂₊ p₁′ p₂′ r₂′)  = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO₂ preserves WHNF and goes from WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app _)  (app₁₊ p₁ r₁)      = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂₋ p₁′ ¬p₂ r₂) = app p₁
naxnf-⇒ (app p₁) (app₂₊ p₁′ p₂ r₂)  = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e′
whnf-⇒ (lam₋ ¬p r)       = lam
whnf-⇒ (lam₊ p r)        = lam
whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app (naxnf-⇒ p₁ r₁))
whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
whnf-⇒ (app₂₊ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))

rev-whnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → WHNF e
rev-whnf-⇒ (lam₋ ¬p r)       = lam
rev-whnf-⇒ (lam₊ p r)        = lam
rev-whnf-⇒ (app₁₊ p₁ r₁)     = whnf (app p₁)
rev-whnf-⇒ (app₂₋ p₁ ¬p₂ r₂) = whnf (app (naxnf←nanf p₁))
rev-whnf-⇒ (app₂₊ p₁ p₂ r₂)  = whnf (app (naxnf←nanf p₁))


---------------------------------------------------------------------------------------------------------------
