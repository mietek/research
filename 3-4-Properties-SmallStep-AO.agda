---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-AO

module 3-4-Properties-SmallStep-AO where

open import 1-4-Semantics-SmallStep
open AO public


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (_ , applam p₁′ p₂′) → case p₁ of λ ()
                            ; (_ , app₁ r₁)        → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁ r₂)     → (_ , r₂) ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : NF e₁) (p₂ : NF e₂) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ p₂ })
rev-applam p₁ p₂ (applam p₁′ p₂′) = refl , applam & uniq-nf p₁′ p₁ ⊗ uniq-nf p₂′ p₂
rev-applam p₁ p₂ (app₁ (lam r₁))  = (_ , r₁) ↯ nrf←nf p₁
rev-applam p₁ p₂ (app₂ p₁′ r₂)    = (_ , r₂) ↯ nrf←nf p₂

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
rev-app₂ p₁ (app₁ (lam r₁))     = (_ , r₁) ↯ nrf←nf p₁
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
... | inj₁ (p₁ , p₂ , q₁ , q₂)                                  = (_ , r₁) ↯ nrf←nf p₁
... | inj₂ (inj₁ (_ , r₁′ , refl , refl))                       = app₁ & uniq-⇒ (lam r₁) (lam r₁′)
... | inj₂ (inj₂ (_ , p₁ , r₂ , refl , refl))                   = (_ , r₁) ↯ nrf←nf p₁
uniq-⇒ {e = app (lam _) _}   (app₂ (lam p₁) r₂) r′             with rev-app₂ p₁ r′
... | inj₁ (p₂ , q₁ , q₂)                                       = (_ , r₂) ↯ nrf←nf p₂
... | inj₂ (_ , r₂′ , refl , refl)                              = app₂ & refl ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (app₂ (nf ()) r₂)  r′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₁ r₁′)     = app₁ & uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←nf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₁ r₁′)     = (_ , r₁′) ↯ nrf←nf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-nf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is deterministic, confluent, and gives rise to a deterministic evaluation relation

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)            (lam r′)             = lam & det-⇒ r r′
det-⇒ (applam p₁ p₂)     (applam p₁′ p₂′)     = refl
det-⇒ (applam p₁ p₂)     (app₁ (lam r₁′))     = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)     (app₂ p₁′ r₂′)       = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₁ (lam r₁))    (applam p₁′ p₂′)     = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (app₁ r₁)          (app₁ r₁′)           = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ r₁)          (app₂ p₁′ r₂′)       = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (app₂ p₁ r₂)       (applam p₁′ p₂′)     = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ p₁ r₂)       (app₁ r₁′)           = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (app₂ p₁ r₂)       (app₂ p₁′ r₂′)       = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open DeterminismOfEvaluation _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO preserves NF

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app () p₂) (applam p₁′ p₂′)
nanf-⇒ (app p₁ p₂) (app₁ r₁)        = app (nanf-⇒ p₁ r₁) p₂
nanf-⇒ (app p₁ p₂) (app₂ p₁′ r₂)    = (_ , r₂) ↯ nrf←nf p₂

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←nf p
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
