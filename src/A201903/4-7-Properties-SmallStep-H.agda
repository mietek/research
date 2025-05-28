{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H

module A201903.4-7-Properties-SmallStep-H where

open import A201903.2-2-Semantics-SmallStep
open H public


---------------------------------------------------------------------------------------------------------------
--
-- SS-H contains SS-CBN

cbn-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ CBN.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
cbn-app₁ CBN.applam    = app₁ app applam
cbn-app₁ (CBN.app₁ r₁) = app₁ app (cbn-app₁ r₁)

h←cbn : ∀ {n} {e : Tm n} {e′} → e CBN.⇒ e′ → e ⇒ e′
h←cbn CBN.applam    = applam
h←cbn (CBN.app₁ r₁) = cbn-app₁ r₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-H contains SS-H₂

h←h₂ : ∀ {n} {e : Tm n} {e′} → e H₂.⇒ e′ → e ⇒ e′
h←h₂ (H₂.cbn-lam ¬p r) = lam (h←cbn r)
h←h₂ (H₂.lam p r)      = lam (h←h₂ r)
h←h₂ (H₂.app₁ p₁ r₁)   = app₁ (na←naxnf p₁) (h←h₂ r₁)


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-H-reducible or HNF

data RF? {n} : Pred₀ (Tm n) where
  yës : ∀ {e} → RF e → RF? e
  nö  : ∀ {e} → HNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var s x)              = nö (hnf var)
rf? (lam s e)              with rf? e
... | yës (_ , r)          = yës (_ , lam r)
... | nö p                 = nö (lam p)
rf? (app e₁ e₂)            with rf? e₁
... | yës (_ , applam)     = yës (_ , app₁ app applam)
... | yës (_ , lam r₁)     = yës (_ , applam)
... | yës (_ , app₁ p₁ r₁) = yës (_ , app₁ app (app₁ p₁ r₁))
... | nö (lam p₁)          = yës (_ , applam)
... | nö (hnf p₁)          = nö (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-H reductions that may terminate at a HNF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ HNF ]⟨ i ⟩
eval e            with rf? e
... | yës (_ , r) = r ◅ λ where .force → eval _
... | nö p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-H does not reduce HNF

hnf←nrf : ∀ {n} {e : Tm n} → NRF e → HNF e
hnf←nrf p        with rf? _
... | yës (_ , r) = r ↯ p
... | nö p′       = p′

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ ()
nrf←naxnf (app p₁) = λ { (applam)      → case p₁ of λ ()
                        ; (app₁ p₁′ r₁) → r₁ ↯ nrf←naxnf p₁ }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (lam r) → r ↯ nrf←hnf p }
nrf←hnf (hnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-H is unique

rev-applam : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (r : app (lam s e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam })
rev-applam applam       = refl , refl
rev-applam (app₁ () r₁)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _}         ()           ()
uniq-⇒ {e = lam _ _}         (lam r)      (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _ _) _} (app₁ p₁ ()) r′
uniq-⇒ {e = app (lam _ _) _} applam       r′             with rev-applam r′
... | refl , refl                                         = refl
uniq-⇒ {e = app (lam _ _) _} (app₁ () r₁) r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H is deterministic, confluent and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ (lam r)      (lam r′)       = lam & refl ⊗ det-⇒ r r′
det-⇒ (app₁ () r₁) applam
det-⇒ (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-H preserves HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ p₁′ r₁) = r₁ ↯ nrf←naxnf p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = r ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
