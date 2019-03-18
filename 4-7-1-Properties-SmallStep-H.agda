---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H

module 4-7-1-Properties-SmallStep-H where

open import 2-2-Semantics-SmallStep
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

app₁₊ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₊ var      r₁ = app₁ var r₁
app₁₊ (app p₁) r₁ = app₁ app r₁

h←h₂ : ∀ {n} {e : Tm n} {e′} → e H₂.⇒ e′ → e ⇒ e′
h←h₂ (H₂.lam₋ ¬p r)   = lam (h←cbn r)
h←h₂ (H₂.lam₊ p r)    = lam (h←h₂ r)
h←h₂ (H₂.app₁₊ p₁ r₁) = app₁₊ p₁ (h←h₂ r₁)


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-H-reducible or HNF

data RF? {n} : Pred₀ (Tm n) where
  yes : ∀ {e} → RF e → RF? e
  no  : ∀ {e} → HNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var x)                = no (hnf var)
rf? (lam e)                with rf? e
... | yes (_ , r)          = yes (_ , lam r)
... | no p                 = no (lam p)
rf? (app e₁ e₂)            with rf? e₁
... | yes (_ , lam r₁)     = yes (_ , applam)
... | yes (_ , applam)     = yes (_ , app₁ app applam)
... | yes (_ , app₁ p₁ r₁) = yes (_ , app₁ app (app₁ p₁ r₁))
... | no (lam p₁)          = yes (_ , applam)
... | no (hnf p₁)          = no (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-H reductions that may terminate at a HNF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ HNF ]⟨ i ⟩
eval e            with rf? e
... | yes (_ , r) = r ◅ λ where .force → eval _
... | no p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-H does not reduce HNF

hnf←nrf : ∀ {n} {e : Tm n} → NRF e → HNF e
hnf←nrf p        with rf? _
... | yes (_ , r) = r ↯ p
... | no p′       = p′

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

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam })
rev-applam applam       = refl , refl
rev-applam (app₁ () r₁)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()           ()
uniq-⇒ {e = lam _}           (lam r)      (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ p₁ ()) r′
uniq-⇒ {e = app (lam _) _}   applam       r′             with rev-applam r′
... | refl , refl                                         = refl
uniq-⇒ {e = app (lam _) _}   (app₁ () r₁) r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H is deterministic, confluent and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)      (lam r′)       = lam & det-⇒ r r′
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
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
