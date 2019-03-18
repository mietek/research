---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-CBN

module 4-1-Properties-SmallStep-CBN where

open import 2-2-Semantics-SmallStep
open CBN public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBN-reducible or WHNF

data RF? {n} : Pred₀ (Tm n) where
  yes : ∀ {e} → RF e → RF? e
  no  : ∀ {e} → WHNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var x)        = no (whnf var)
rf? (lam e)        = no lam
rf? (app e₁ e₂)    with rf? e₁
... | yes (_ , r₁) = yes (_ , app₁ r₁)
... | no lam       = yes (_ , applam)
... | no (whnf p₁) = no (whnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-CBN reductions that may terminate at a WHNF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ WHNF ]⟨ i ⟩
eval e            with rf? e
... | yes (_ , r) = r ◅ λ where .force → eval _
... | no p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN does not reduce WHNF

whnf←nrf : ∀ {n} {e : Tm n} → NRF e → WHNF e
whnf←nrf p       with rf? _
... | yes (_ , r) = r ↯ p
... | no p′       = p′

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ ()
nrf←naxnf (app p₁) = λ { applam    → case p₁ of λ ()
                        ; (app₁ r₁) → r₁ ↯ nrf←naxnf p₁ }

nrf←whnf : ∀ {n} {e : Tm n} → WHNF e → NRF e
nrf←whnf lam      = λ ()
nrf←whnf (whnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam })
rev-applam applam    = refl , refl
rev-applam (app₁ ())

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()        ()
uniq-⇒ {e = lam _}           ()        ()
uniq-⇒ {e = app (var _) _}   (app₁ ()) (app₁ ())
uniq-⇒ {e = app (lam _) _}   applam    r′        with rev-applam r′
... | refl , refl                                 = refl
uniq-⇒ {e = app (lam _) _}   (app₁ ()) r′
uniq-⇒ {e = app (app _ _) _} (app₁ r)  (app₁ r′) = app₁ & uniq-⇒ r r′


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ applam    applam    = refl
det-⇒ applam    (app₁ ())
det-⇒ (app₁ ()) applam
det-⇒ (app₁ r)  (app₁ r′) = app & det-⇒ r r′ ⊗ refl

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBN preserves WHNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) applam
naxnf-⇒ (app p₁) (app₁ r₁) = app (naxnf-⇒ p₁ r₁)

whnf-⇒ : ∀ {n} {e : Tm n} {e′} → WHNF e → e ⇒ e′ → WHNF e′
whnf-⇒ lam      ()
whnf-⇒ (whnf p) r  = whnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
