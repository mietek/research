{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-NO

module A201903.4-2-Properties-SmallStep-NO where

open import A201903.2-2-Semantics-SmallStep
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

no←no₂ : ∀ {n} {e : Tm n} {e′} → e NO₂.⇒ e′ → e ⇒ e′
no←no₂ (NO₂.cbn-lam ¬p r)       = lam (no←cbn r)
no←no₂ (NO₂.lam p r)            = lam (no←no₂ r)
no←no₂ (NO₂.app₁ p₁ r₁)         = app₁ (na←naxnf p₁) (no←no₂ r₁)
no←no₂ (NO₂.cbn-app₂ p₁ ¬p₂ r₂) = app₂ p₁ (no←cbn r₂)
no←no₂ (NO₂.app₂ p₁ p₂ r₂)      = app₂ p₁ (no←no₂ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-NO-reducible or NF

data RF? {n} : Pred₀ (Tm n) where
  yës : ∀ {e} → RF e → RF? e
  nö  : ∀ {e} → NF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var s x)                             = nö (nf var)
rf? (lam s e)                             with rf? e
... | yës (_ , r)                         = yës (_ , lam r)
... | nö p                                = nö (lam p)
rf? (app e₁ e₂)                           with rf? e₁ | rf? e₂
... | yës (_ , applam)     | _            = yës (_ , app₁ app applam)
... | yës (_ , lam r₁)     | _            = yës (_ , applam)
... | yës (_ , app₁ p₁ r₁) | _            = yës (_ , app₁ app (app₁ p₁ r₁))
... | yës (_ , app₂ p₁ r₂) | _            = yës (_ , app₁ app (app₂ p₁ r₂))
... | nö (lam p₁)          | _            = yës (_ , applam)
... | nö (nf p₁)           | yës (_ , r₂) = yës (_ , app₂ p₁ r₂)
... | nö (nf p₁)           | nö p₂        = nö (nf (app p₁ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-NO reductions that may terminate at a NF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ NF ]⟨ i ⟩
eval e            with rf? e
... | yës (_ , r) = r ◅ λ where .force → eval _
... | nö p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO does not reduce NF

nf←nrf : ∀ {n} {e : Tm n} → NRF e → NF e
nf←nrf p         with rf? _
... | yës (_ , r) = r ↯ p
... | nö p′       = p′

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { applam        → case p₁ of λ ()
                            ; (app₁ p₁′ r₁) → r₁ ↯ nrf←nanf p₁
                            ; (app₂ p₁′ r₂) → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is unique

rev-applam : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (r : app (lam s e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam })
rev-applam applam       = refl , refl
rev-applam (app₁ () r₁)
rev-applam (app₂ () r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _}         ()           ()
uniq-⇒ {e = lam _ _}         (lam r)      (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _ _) _} (app₁ p₁ ()) r′
uniq-⇒ {e = app (var _ _) _} (app₂ p₁ r₂) (app₁ p₁′ ())
uniq-⇒ {e = app (var _ _) _} (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _ _) _} applam       r′             with rev-applam r′
... | refl , refl                                         = refl
uniq-⇒ {e = app (lam _ _) _} (app₁ () r₁) r′
uniq-⇒ {e = app (lam _ _) _} (app₂ () r₂) r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂) (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-NO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ applam       (app₂ () r₂′)
det-⇒ (lam r)      (lam r′)       = lam & refl ⊗ det-⇒ r r′
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
