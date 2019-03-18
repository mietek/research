---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-CBV

module 4-3-Properties-SmallStep-CBV where

open import 2-2-Semantics-SmallStep
open CBV public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBV-reducible or WNF

data RF? {n} : Pred₀ (Tm n) where
  yes : ∀ {e} → RF e → RF? e
  no  : ∀ {e} → WNF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var x)                       = no (wnf var)
rf? (lam e)                       = no lam
rf? (app e₁ e₂)                   with rf? e₁ | rf? e₂
... | yes (_ , r₁) | _            = yes (_ , app₁ r₁)
... | no lam       | yes (_ , r₂) = yes (_ , app₂ lam r₂)
... | no lam       | no p₂        = yes (_ , applam p₂)
... | no (wnf p₁)  | yes (_ , r₂) = yes (_ , app₂ (wnf p₁) r₂)
... | no (wnf p₁)  | no p₂        = no (wnf (app p₁ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV does not reduce WNF

wnf←nrf : ∀ {n} {e : Tm n} → NRF e → WNF e
wnf←nrf p        with rf? _
... | yes (_ , r) = r ↯ p
... | no p′       = p′

mutual
  nrf←wnf : ∀ {n} {e : Tm n} → WNF e → NRF e
  nrf←wnf lam     = λ ()
  nrf←wnf (wnf p) = nrf←nawnf p

  nrf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NRF e
  nrf←nawnf var         = λ ()
  nrf←nawnf (app p₁ p₂) = λ { (applam p₂′)   → case p₁ of λ ()
                             ; (app₁ r₁′)     → r₁′ ↯ nrf←nawnf p₁
                             ; (app₂ p₁′ r₂′) → r₂′ ↯ nrf←wnf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₂ : WNF e₂) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₂ })
rev-applam p₂ (applam p₂′) = refl , applam & uniq-wnf p₂′ p₂
rev-applam p₂ (app₁ ())
rev-applam p₂ (app₂ p₁ r₂) = r₂ ↯ nrf←wnf p₂

rev-app₂ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (r : app (lam e₁) e₂ ⇒ e′) →
           (∃ λ p₂ →
             Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₂ }) ⊎
           (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
             Σ (e₂ ⇒ e₂′) λ r₂ →
               Σ (e′ ≡ app (lam e₁) e₂′) λ { refl →
                 r ≡ app₂ lam r₂ })
rev-app₂ (applam p₂)        = inj₁ (p₂ , refl , refl)
rev-app₂ (app₁ ())
rev-app₂ (app₂ lam r₂)      = inj₂ (_ , r₂ , refl , refl)
rev-app₂ (app₂ (wnf ()) r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()                 ()
uniq-⇒ {e = lam _}           ()                 ()
uniq-⇒ {e = app (var _) _}   (app₁ ())          r′
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)       (app₁ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-wnf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (applam p₂)        r′             with rev-applam p₂ r′
... | refl , refl                                               = refl
uniq-⇒ {e = app (lam _) _}   (app₁ ())          r′
uniq-⇒ {e = app (lam _) _}   (app₂ lam r₂)      r′             with rev-app₂ r′
... | inj₁ (p₂ , q₁ , q₂)                                       = r₂ ↯ nrf←wnf p₂
... | inj₂ (_ , r₂′ , refl , refl)                              = app₂ & refl ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (app₂ (wnf ()) r₂) r′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₁ r₁′)     = app₁ & uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₂ p₁′ r₂′) = r₁ ↯ nrf←wnf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₁ r₁′)     = r₁′ ↯ nrf←wnf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-wnf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (applam p₂)  (applam p₂′)   = refl
det-⇒ (applam p₂)  (app₁ ())
det-⇒ (applam p₂)  (app₂ p₁′ r₂′) = r₂′ ↯ nrf←wnf p₂
det-⇒ (app₁ ())    (applam p₂′)
det-⇒ (app₁ r₁)    (app₁ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)    (app₂ p₁′ r₂′) = r₁ ↯ nrf←wnf p₁′
det-⇒ (app₂ p₁ r₂) (applam p₂′)   = r₂ ↯ nrf←wnf p₂′
det-⇒ (app₂ p₁ r₂) (app₁ r₁′)     = r₁′ ↯ nrf←wnf p₁
det-⇒ (app₂ p₁ r₂) (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV preserves WNF

nawnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇒ e′ → NAWNF e′
nawnf-⇒ var         ()
nawnf-⇒ (app () p₂) (applam p₂′)
nawnf-⇒ (app p₁ p₂) (app₁ r₁)     = app (nawnf-⇒ p₁ r₁) p₂
nawnf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = r₂ ↯ nrf←wnf p₂

wnf-⇒ : ∀ {n} {e : Tm n} {e′} → WNF e → e ⇒ e′ → WNF e′
wnf-⇒ lam     ()
wnf-⇒ (wnf p) r  = wnf (nawnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
