---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-CBV

module 4-3-Properties-SmallStep-CBV where

open import 2-2-Semantics-SmallStep
open CBV public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-CBV-reducible, NAWNF, or WNF

data Form : ∀ {n} → Pred₀ (Tm n) where
  rf    : ∀ {n} {e : Tm n} → RF e → Form e
  nawnf : ∀ {n} {e : Tm n} → NAWNF e → Form e
  wnf   : ∀ {n} {e : Tm n} → ¬ NAWNF e → WNF e → Form e

form? : ∀ {n} (e : Tm n) → Form e
form? (var x)                        = nawnf var
form? (lam e)                        = wnf (λ ()) lam
form? (app e₁ e₂)                    with form? e₁ | form? e₂
... | rf (_ , r₁)      | _           = rf (_ , app₁ r₁)
... | nawnf p₁         | rf (_ , r₂) = rf (_ , app₂ (wnf p₁) r₂)
... | nawnf p₁         | nawnf p₂    = nawnf (app p₁ (wnf p₂))
... | nawnf p₁         | wnf _ p₂    = nawnf (app p₁ p₂)
... | wnf _ lam        | rf (_ , r₂) = rf (_ , app₂ lam r₂)
... | wnf _ lam        | nawnf p₂    = rf (_ , applam (wnf p₂))
... | wnf _ lam        | wnf _ p₂    = rf (_ , applam p₂)
... | wnf ¬p₁ (wnf p₁) | _           = p₁ ↯ ¬p₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-CBV does not reduce WNF

mutual
  nrf←wnf : ∀ {n} {e : Tm n} → WNF e → NRF e
  nrf←wnf lam     = λ ()
  nrf←wnf (wnf p) = nrf←nawnf p

  nrf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NRF e
  nrf←nawnf var         = λ ()
  nrf←nawnf (app p₁ p₂) = λ { (applam p₂′)   → case p₁ of λ ()
                             ; (app₁ r₁′)     → r₁′ ↯ nrf←nawnf p₁
                             ; (app₂ p₁′ r₂′) → r₂′ ↯ nrf←wnf p₂ }

wnf←nrf : ∀ {n} {e : Tm n} → NRF e → WNF e
wnf←nrf p       with form? _
... | rf (_ , r) = r ↯ p
... | nawnf p′   = wnf p′
... | wnf _ p′   = p′


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
