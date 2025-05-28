{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HS

module A201903.4-6-Properties-SmallStep-HS where

open import A201903.2-2-Semantics-SmallStep
open HS public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-HS-reducible or HNF

data RF? {n} : Pred₀ (Tm n) where
  yës : ∀ {e} → RF e → RF? e
  nö  : ∀ {e} → HNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var s x)      = nö (hnf var)
rf? (lam s e)      with rf? e
... | yës (_ , r)  = yës (_ , lam r)
... | nö p         = nö (lam p)
rf? (app e₁ e₂)    with rf? e₁
... | yës (_ , r₁) = yës (_ , app₁ r₁)
... | nö (lam p₁)  = yës (_ , applam p₁)
... | nö (hnf p₁)  = nö (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-HS reductions that may terminate at a HNF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ HNF ]⟨ i ⟩
eval e            with rf? e
... | yës (_ , r) = r ◅ λ where .force → eval _
... | nö p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS does not reduce HNF

hnf←nrf : ∀ {n} {e : Tm n} → NRF e → HNF e
hnf←nrf p        with rf? _
... | yës (_ , r) = r ↯ p
... | nö p′       = p′

nrf←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NRF e
nrf←naxnf var      = λ ()
nrf←naxnf (app p₁) = λ { (applam p₁′) → case p₁ of λ ()
                        ; (app₁ r₁)    → r₁ ↯ nrf←naxnf p₁ }

nrf←hnf : ∀ {n} {e : Tm n} → HNF e → NRF e
nrf←hnf (lam p) = λ { (lam r) → r ↯ nrf←hnf p }
nrf←hnf (hnf p) = nrf←naxnf p


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS is unique

rev-applam : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : HNF e₁) (r : app (lam s e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ })
rev-applam p₁ (applam p₁′)    = refl , applam & uniq-hnf p₁′ p₁
rev-applam p₁ (app₁ (lam r₁)) = r₁ ↯ nrf←hnf p₁

rev-app₁ : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (r : app (lam s e₁) e₂ ⇒ e′) →
           (∃ λ p₁ →
             Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ }) ⊎
           (Σ {_} {0ᴸ} (Tm (suc n)) λ e₁′ →
             Σ (e₁ ⇒ e₁′) λ r₁ →
               Σ (e′ ≡ app (lam s e₁′) e₂) λ { refl →
                 r ≡ app₁ (lam r₁) })
rev-app₁ (applam p₁)     = inj₁ (p₁ , refl , refl)
rev-app₁ (app₁ (lam r₁)) = inj₂ (_ , r₁ , refl , refl)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _}         ()              ()
uniq-⇒ {e = lam _ _}         (lam r)         (lam r′)   = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _ _) _} (app₁ ())       r′
uniq-⇒ {e = app (lam _ _) _} (applam p₁)     r′         with rev-applam p₁ r′
... | refl , refl                                        = refl
uniq-⇒ {e = app (lam _ _) _} (app₁ (lam r₁)) r′         with rev-app₁ r′
... | inj₁ (p₁ , q₁ , q₂)                                = r₁ ↯ nrf←hnf p₁
... | inj₂ (_ , r₁′ , refl , refl)                       = app₁ & uniq-⇒ (lam r₁) (lam r₁′)
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)       (app₁ r₁′) = app₁ & uniq-⇒ r₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HS is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (applam p₁)     (applam p₁′)     = refl
det-⇒ (applam p₁)     (app₁ (lam r₁′)) = r₁′ ↯ nrf←hnf p₁
det-⇒ (lam r)         (lam r′)         = lam & refl ⊗ det-⇒ r r′
det-⇒ (app₁ (lam r₁)) (applam p₁′)     = r₁ ↯ nrf←hnf p₁′
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
naxnf-⇒ (app p₁) (app₁ r₁)    = r₁ ↯ nrf←naxnf p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = r ↯ nrf←hnf p
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)

rev-¬hnf-⇒ : ∀ {n} {e : Tm n} {e′} → e ⇒ e′ → ¬ HNF e
rev-¬hnf-⇒ r = λ p → r ↯ nrf←hnf p


---------------------------------------------------------------------------------------------------------------
