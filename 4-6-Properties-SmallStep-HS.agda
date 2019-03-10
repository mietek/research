---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HS

module 4-6-Properties-SmallStep-HS where

open import 2-2-Semantics-SmallStep
open HS public


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS does not reduce HNF

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ ()
nrf←naxnf (app p₁) = λ { (_ , applam p₁′) → case p₁ of λ ()
                        ; (_ , app₁ r₁)    → (_ , r₁) ↯ nrf←naxnf p₁ }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←hnf p }
nrf←hnf (hnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : HNF e₁) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ })
rev-applam p₁ (applam p₁′)    = refl , applam & uniq-hnf p₁′ p₁
rev-applam p₁ (app₁ (lam r₁)) = (_ , r₁) ↯ nrf←hnf p₁

rev-app₁ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (r : app (lam e₁) e₂ ⇒ e′) →
           (∃ λ p₁ →
             Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ }) ⊎
           (Σ {_} {0ᴸ} (Tm (suc n)) λ e₁′ →
             Σ (e₁ ⇒ e₁′) λ r₁ →
               Σ (e′ ≡ app (lam e₁′) e₂) λ { refl →
                 r ≡ app₁ (lam r₁) })
rev-app₁ (applam p₁)     = inj₁ (p₁ , refl , refl)
rev-app₁ (app₁ (lam r₁)) = inj₂ (_ , r₁ , refl , refl)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()              ()
uniq-⇒ {e = lam _}           (lam r)         (lam r′)   = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ ())       r′
uniq-⇒ {e = app (lam _) _}   (applam p₁)     r′         with rev-applam p₁ r′
... | refl , refl                                        = refl
uniq-⇒ {e = app (lam _) _}   (app₁ (lam r₁)) r′         with rev-app₁ r′
... | inj₁ (p₁ , q₁ , q₂)                                = (_ , r₁) ↯ nrf←hnf p₁
... | inj₂ (_ , r₁′ , refl , refl)                       = app₁ & uniq-⇒ (lam r₁) (lam r₁′)
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)       (app₁ r₁′) = app₁ & uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)         (lam r′)         = lam & det-⇒ r r′
det-⇒ (applam p₁)     (applam p₁′)     = refl
det-⇒ (applam p₁)     (app₁ (lam r₁′)) = (_ , r₁′) ↯ nrf←hnf p₁
det-⇒ (app₁ (lam r₁)) (applam p₁′)     = (_ , r₁) ↯ nrf←hnf p₁′
det-⇒ (app₁ r₁)       (app₁ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS preserves HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) (applam p₁′)
naxnf-⇒ (app p₁) (app₁ r₁)    = (_ , r₁) ↯ nrf←naxnf p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)

rev-¬hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → ¬ HNF e
rev-¬hnf-⇒ r = λ p → (_ , r) ↯ nrf←hnf p


---------------------------------------------------------------------------------------------------------------