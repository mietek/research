---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-H

module 3-7-1-Properties-SmallStep-H where

open import 1-4-Semantics-SmallStep
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
-- SS-H does not reduce HNF

open NonReducibleForms _⇒_ public

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ ()
nrf←naxnf (app p₁) = λ { (_ , applam)      → case p₁ of λ ()
                        ; (_ , app₁ p₁′ r₁) → (_ , r₁) ↯ nrf←naxnf p₁ }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←hnf p }
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

uniq-⇒ : Unique² _⇒_
uniq-⇒ {e = var _}           ()           ()
uniq-⇒ {e = lam _}           (lam r)      (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ p₁ ()) r′
uniq-⇒ {e = app (lam _) _}   applam       r′             with rev-applam r′
... | refl , refl                                         = refl
uniq-⇒ {e = app (lam _) _}   (app₁ () r₁) r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-H is deterministic, confluent and has unique non-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)      (lam r′)       = lam & det-⇒ r r′
det-⇒ applam       applam         = refl
det-⇒ applam       (app₁ () r₁′)
det-⇒ (app₁ () r₁) applam
det-⇒ (app₁ p₁ r₁) (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-H preserves HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ p₁′ r₁) = (_ , r₁) ↯ nrf←naxnf p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
