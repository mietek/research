---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO

module 4-2-1-Properties-SmallStep-NO where

open import 2-2-Semantics-SmallStep
open NO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO contains SS-CBN

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁ app applam
cbn-app₁ (CBN.app₁ r₁) = app₁ app (cbn-app₁ r₁)

no←cbn : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
no←cbn CBN.applam    = applam
no←cbn (CBN.app₁ r₁) = cbn-app₁ r₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO contains SS-NO₂

app₁₊ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₊ var      r₁ = app₁ var r₁
app₁₊ (app p₁) r₁ = app₁ app r₁

no←no₂ : ∀ {n} {e : Tm n} {e′} → e NO₂.⇒ e′ → e ⇒ e′
no←no₂ (NO₂.lam₋ ¬p r)       = lam (no←cbn r)
no←no₂ (NO₂.lam₊ p r)        = lam (no←no₂ r)
no←no₂ (NO₂.app₁₊ p₁ r₁)     = app₁₊ p₁ (no←no₂ r₁)
no←no₂ (NO₂.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (no←cbn r₂)
no←no₂ (NO₂.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (no←no₂ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-NO reducible, NANF, or NF

data Form : ∀ {n} → Pred₀ (Tm n) where
  rf   : ∀ {n} {e : Tm n} → RF e → Form e
  nanf : ∀ {n} {e : Tm n} → NANF e → Form e
  nf   : ∀ {n} {e : Tm n} → ¬ NANF e → NF e → Form e

form? : ∀ {n} (e : Tm n) → Form e
form? (var x)                           = nanf var
form? (lam e)                           with form? e
... | rf (_ , r)                        = rf (_ , lam r)
... | nanf p                            = nf (λ ()) (lam (nf p))
... | nf _ p                            = nf (λ ()) (lam p)
form? (app e₁ e₂)                       with form? e₁ | form? e₂
... | rf (_ , lam r₁)     | _           = rf (_ , applam)
... | rf (_ , applam)     | _           = rf (_ , app₁ app applam)
... | rf (_ , app₁ p₁ r₁) | _           = rf (_ , app₁ app (app₁ p₁ r₁))
... | rf (_ , app₂ p₁ r₂) | _           = rf (_ , app₁ app (app₂ p₁ r₂))
... | nanf p₁             | rf (_ , r₂) = rf (_ , app₂ p₁ r₂)
... | nanf p₁             | nanf p₂     = nanf (app p₁ (nf p₂))
... | nanf p₁             | nf _ p₂     = nanf (app p₁ p₂)
... | nf _ (lam p₁)       | _           = rf (_ , applam)
... | nf ¬p₁ (nf p₁)      | _           = p₁ ↯ ¬p₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO does not reduce NF

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { applam        → case p₁ of λ ()
                            ; (app₁ p₁′ r₁) → r₁ ↯ nrf←nanf p₁
                            ; (app₂ p₁′ r₂) → r₂ ↯ nrf←nf p₂ }

nf←nrf : ∀ {n} {e : Tm n} → NRF e → NF e
nf←nrf p        with form? _
... | rf (_ , r) = r ↯ p
... | nanf p′    = nf p′
... | nf _ p′    = p′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam })
rev-applam applam       = refl , refl
rev-applam (app₁ () r₁)
rev-applam (app₂ () r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()           ()
uniq-⇒ {e = lam _}           (lam r)      (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ p₁ ()) r′
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂) (app₁ p₁′ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   applam       r′             with rev-applam r′
... | refl , refl                                         = refl
uniq-⇒ {e = app (lam _) _}   (app₁ () r₁) r′
uniq-⇒ {e = app (lam _) _}   (app₂ () r₂) r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂) (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)      (lam r′)       = lam & det-⇒ r r′
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ applam       (app₂ () r₂′)
det-⇒ (app₁ () r₁) applam
det-⇒ (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁) (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂) applam
det-⇒ (app₂ p₁ r₂) (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO preserves WHNF and NF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ p₁′ r₁) = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂ p₁′ r₂) = app p₁

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      (lam r) = lam
whnf-⇒ (whnf p) r       = whnf (naxnf-⇒ p r)

mutual
  nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
  nf-⇒ (lam p) (lam r) = lam (nf-⇒ p r)
  nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)

  nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
  nanf-⇒ var         ()
  nanf-⇒ (app () p₂) applam
  nanf-⇒ (app p₁ p₂) (app₁ p₁′ r₁) = app (nanf-⇒ p₁ r₁) p₂
  nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = app p₁′ (nf-⇒ p₂ r₂)


---------------------------------------------------------------------------------------------------------------
