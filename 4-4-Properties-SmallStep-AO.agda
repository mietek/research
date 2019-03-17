---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-AO

module 4-4-Properties-SmallStep-AO where

open import 2-2-Semantics-SmallStep
open AO public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-AO-reducible, NANF, or NF

data Form : ∀ {n} → Pred₀ (Tm n) where
  rf   : ∀ {n} {e : Tm n} → RF e → Form e
  nanf : ∀ {n} {e : Tm n} → NANF e → Form e
  nf   : ∀ {n} {e : Tm n} → ¬ NANF e → NF e → Form e

form? : ∀ {n} (e : Tm n) → Form e
form? (var x)                             = nanf var
form? (lam e)                             with form? e
... | rf (_ , r)                          = rf (_ , lam r)
... | nanf p                              = nf (λ ()) (lam (nf p))
... | nf _ p                              = nf (λ ()) (lam p)
form? (app e₁ e₂)                         with form? e₁ | form? e₂
... | rf (_ , lam r₁)       | _           = rf (_ , app₁ (lam r₁))
... | rf (_ , applam p₁ p₂) | _           = rf (_ , app₁ (applam p₁ p₂))
... | rf (_ , app₁ r₁)      | _           = rf (_ , app₁ (app₁ r₁))
... | rf (_ , app₂ p₁ r₂)   | _           = rf (_ , app₁ (app₂ p₁ r₂))
... | nanf p₁               | rf (_ , r₂) = rf (_ , app₂ (nf p₁) r₂)
... | nanf p₁               | nanf p₂     = nanf (app p₁ (nf p₂))
... | nanf p₁               | nf _ p₂     = nanf (app p₁ p₂)
... | nf _ (lam p₁)         | rf (_ , r₂) = rf (_ , app₂ (lam p₁) r₂)
... | nf _ (lam p₁)         | nanf p₂     = rf (_ , applam p₁ (nf p₂))
... | nf _ (lam p₁)         | nf _ p₂     = rf (_ , applam p₁ p₂)
... | nf ¬p₁ (nf p₁)        | _           = p₁ ↯ ¬p₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO does not reduce NF

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (applam p₁′ p₂′) → case p₁ of λ ()
                            ; (app₁ r₁)        → r₁ ↯ nrf←nanf p₁
                            ; (app₂ p₁ r₂)     → r₂ ↯ nrf←nf p₂ }

nf←nrf : ∀ {n} {e : Tm n} → NRF e → NF e
nf←nrf p        with form? _
... | rf (_ , r) = r ↯ p
... | nanf p′    = nf p′
... | nf _ p′    = p′


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : NF e₁) (p₂ : NF e₂) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ p₂ })
rev-applam p₁ p₂ (applam p₁′ p₂′) = refl , applam & uniq-nf p₁′ p₁ ⊗ uniq-nf p₂′ p₂
rev-applam p₁ p₂ (app₁ (lam r₁))  = r₁ ↯ nrf←nf p₁
rev-applam p₁ p₂ (app₂ p₁′ r₂)    = r₂ ↯ nrf←nf p₂

rev-app₂ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (p₁ : NF e₁) (r : app (lam e₁) e₂ ⇒ e′) →
           (∃ λ p₂ →
             Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ p₂ }) ⊎
           (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
             Σ (e₂ ⇒ e₂′) λ r₂ →
               Σ (e′ ≡ app (lam e₁) e₂′) λ { refl →
                 r ≡ app₂ (lam p₁) r₂ })
rev-app₂ p₁ (applam p₁′ p₂)     = inj₁ (p₂ , refl , applam & uniq-nf p₁′ p₁ ⊗ refl)
rev-app₂ p₁ (app₁ (lam r₁))     = r₁ ↯ nrf←nf p₁
rev-app₂ p₁ (app₂ (lam p₁′) r₂) = inj₂ (_ , r₂ , refl , app₂ & uniq-nf (lam p₁′) (lam p₁) ⊗ refl)
rev-app₂ p₁ (app₂ (nf ()) r₂)

rev-app₁ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (r : app (lam e₁) e₂ ⇒ e′) →
           (∃ λ p₁ →
             ∃ λ p₂ →
               Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
                 r ≡ applam p₁ p₂ }) ⊎
           (Σ {_} {0ᴸ} (Tm (suc n)) λ e₁′ →
             Σ (e₁ ⇒ e₁′) λ r₁ →
               Σ (e′ ≡ app (lam e₁′) e₂) λ { refl →
                 r ≡ app₁ (lam r₁) }) ⊎
           (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
             Σ {_} {0ᴸ} (NF e₁) λ p₁ →
               Σ (e₂ ⇒ e₂′) λ r₂ →
                 Σ (e′ ≡ app (lam e₁) e₂′) λ { refl →
                   r ≡ app₂ (lam p₁) r₂ })
rev-app₁ (applam p₁ p₂)     = inj₁ (p₁ , p₂ , refl , refl)
rev-app₁ (app₁ (lam r₁))    = inj₂ (inj₁ (_ , r₁ , refl , refl))
rev-app₁ (app₂ (lam p₁) r₂) = inj₂ (inj₂ (_ , p₁ , r₂ , refl , refl))
rev-app₁ (app₂ (nf ()) r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()                 ()
uniq-⇒ {e = lam _}           (lam r)            (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ ())          r′
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)       (app₁ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-nf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (applam p₁ p₂)     r′             with rev-applam p₁ p₂ r′
... | refl , refl                                               = refl
uniq-⇒ {e = app (lam _) _}   (app₁ (lam r₁))    r′             with rev-app₁ r′
... | inj₁ (p₁ , p₂ , q₁ , q₂)                                  = r₁ ↯ nrf←nf p₁
... | inj₂ (inj₁ (_ , r₁′ , refl , refl))                       = app₁ & uniq-⇒ (lam r₁) (lam r₁′)
... | inj₂ (inj₂ (_ , p₁ , r₂ , refl , refl))                   = r₁ ↯ nrf←nf p₁
uniq-⇒ {e = app (lam _) _}   (app₂ (lam p₁) r₂) r′             with rev-app₂ p₁ r′
... | inj₁ (p₂ , q₁ , q₂)                                       = r₂ ↯ nrf←nf p₂
... | inj₂ (_ , r₂′ , refl , refl)                              = app₂ & refl ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (app₂ (nf ()) r₂)  r′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₁ r₁′)     = app₁ & uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₂ p₁′ r₂′) = r₁ ↯ nrf←nf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₁ r₁′)     = r₁′ ↯ nrf←nf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-nf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)         (lam r′)         = lam & det-⇒ r r′
det-⇒ (applam p₁ p₂)  (applam p₁′ p₂′) = refl
det-⇒ (applam p₁ p₂)  (app₁ (lam r₁′)) = r₁′ ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)  (app₂ p₁′ r₂′)   = r₂′ ↯ nrf←nf p₂
det-⇒ (app₁ (lam r₁)) (applam p₁′ p₂′) = r₁ ↯ nrf←nf p₁′
det-⇒ (app₁ r₁)       (app₁ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)       (app₂ p₁′ r₂′)   = r₁ ↯ nrf←nf p₁′
det-⇒ (app₂ p₁ r₂)    (applam p₁′ p₂′) = r₂ ↯ nrf←nf p₂′
det-⇒ (app₂ p₁ r₂)    (app₁ r₁′)       = r₁′ ↯ nrf←nf p₁
det-⇒ (app₂ p₁ r₂)    (app₂ p₁′ r₂′)   = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO preserves NF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) (applam p₁′ p₂′)
nanf-⇒ (app p₁ p₂) (app₁ r₁)        = app (nanf-⇒ p₁ r₁) p₂
nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂)    = r₂ ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = r ↯ nrf←nf p
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
