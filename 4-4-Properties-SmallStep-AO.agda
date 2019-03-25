---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-AO

module 4-4-Properties-SmallStep-AO where

open import 2-2-Semantics-SmallStep
open AO public


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-AO-reducible or NF

data RF? {n} : Pred₀ (Tm n) where
  yes : ∀ {e} → RF e → RF? e
  no  : ∀ {e} → NF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var s x)                               = no (nf var)
rf? (lam s e)                               with rf? e
... | yes (_ , r)                           = yes (_ , lam r)
... | no p                                  = no (lam p)
rf? (app e₁ e₂)                             with rf? e₁ | rf? e₂
... | yes (_ , applam p₁ p₂) | _            = yes (_ , app₁ (applam p₁ p₂))
... | yes (_ , lam r₁)       | _            = yes (_ , app₁ (lam r₁))
... | yes (_ , app₁ r₁)      | _            = yes (_ , app₁ (app₁ r₁))
... | yes (_ , app₂ p₁ r₂)   | _            = yes (_ , app₁ (app₂ p₁ r₂))
... | no (lam p₁)            | yes (_ , r₂) = yes (_ , app₂ (lam p₁) r₂)
... | no (lam p₁)            | no p₂        = yes (_ , applam p₁ p₂)
... | no (nf p₁)             | yes (_ , r₂) = yes (_ , app₂ (nf p₁) r₂)
... | no (nf p₁)             | no p₂        = no (nf (app p₁ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-AO reductions that may terminate at a NF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ NF ]⟨ i ⟩
eval e            with rf? e
... | yes (_ , r) = r ◅ λ where .force → eval _
... | no p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO does not reduce NF

nf←nrf : ∀ {n} {e : Tm n} → NRF e → NF e
nf←nrf p         with rf? _
... | yes (_ , r) = r ↯ p
... | no p′       = p′

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (applam p₁′ p₂′) → case p₁ of λ ()
                            ; (app₁ r₁)        → r₁ ↯ nrf←nanf p₁
                            ; (app₂ p₁ r₂)     → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is unique

rev-applam : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : NF e₁) (p₂ : NF e₂) (r : app (lam s e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ p₂ })
rev-applam p₁ p₂ (applam p₁′ p₂′) = refl , applam & uniq-nf p₁′ p₁ ⊗ uniq-nf p₂′ p₂
rev-applam p₁ p₂ (app₁ (lam r₁))  = r₁ ↯ nrf←nf p₁
rev-applam p₁ p₂ (app₂ p₁′ r₂)    = r₂ ↯ nrf←nf p₂

rev-app₂ : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (p₁ : NF e₁) (r : app (lam s e₁) e₂ ⇒ e′) →
           (∃ λ p₂ →
             Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ p₂ }) ⊎
           (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
             Σ (e₂ ⇒ e₂′) λ r₂ →
               Σ (e′ ≡ app (lam s e₁) e₂′) λ { refl →
                 r ≡ app₂ (lam p₁) r₂ })
rev-app₂ p₁ (applam p₁′ p₂)     = inj₁ (p₂ , refl , applam & uniq-nf p₁′ p₁ ⊗ refl)
rev-app₂ p₁ (app₁ (lam r₁))     = r₁ ↯ nrf←nf p₁
rev-app₂ p₁ (app₂ (lam p₁′) r₂) = inj₂ (_ , r₂ , refl , app₂ & uniq-nf (lam p₁′) (lam p₁) ⊗ refl)
rev-app₂ p₁ (app₂ (nf ()) r₂)

rev-app₁ : ∀ {n s} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
           (r : app (lam s e₁) e₂ ⇒ e′) →
           (∃ λ p₁ →
             ∃ λ p₂ →
               Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
                 r ≡ applam p₁ p₂ }) ⊎
           (Σ {_} {0ᴸ} (Tm (suc n)) λ e₁′ →
             Σ (e₁ ⇒ e₁′) λ r₁ →
               Σ (e′ ≡ app (lam s e₁′) e₂) λ { refl →
                 r ≡ app₁ (lam r₁) }) ⊎
           (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
             Σ {_} {0ᴸ} (NF e₁) λ p₁ →
               Σ (e₂ ⇒ e₂′) λ r₂ →
                 Σ (e′ ≡ app (lam s e₁) e₂′) λ { refl →
                   r ≡ app₂ (lam p₁) r₂ })
rev-app₁ (applam p₁ p₂)     = inj₁ (p₁ , p₂ , refl , refl)
rev-app₁ (app₁ (lam r₁))    = inj₂ (inj₁ (_ , r₁ , refl , refl))
rev-app₁ (app₂ (lam p₁) r₂) = inj₂ (inj₂ (_ , p₁ , r₂ , refl , refl))
rev-app₁ (app₂ (nf ()) r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _ _}         ()                 ()
uniq-⇒ {e = lam _ _}         (lam r)            (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _ _) _} (app₁ ())          r′
uniq-⇒ {e = app (var _ _) _} (app₂ p₁ r₂)       (app₁ ())
uniq-⇒ {e = app (var _ _) _} (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-nf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _ _) _} (applam p₁ p₂)     r′             with rev-applam p₁ p₂ r′
... | refl , refl                                               = refl
uniq-⇒ {e = app (lam _ _) _} (app₁ (lam r₁))    r′             with rev-app₁ r′
... | inj₁ (p₁ , p₂ , q₁ , q₂)                                  = r₁ ↯ nrf←nf p₁
... | inj₂ (inj₁ (_ , r₁′ , refl , refl))                       = app₁ & uniq-⇒ (lam r₁) (lam r₁′)
... | inj₂ (inj₂ (_ , p₁ , r₂ , refl , refl))                   = r₁ ↯ nrf←nf p₁
uniq-⇒ {e = app (lam _ _) _} (app₂ (lam p₁) r₂) r′             with rev-app₂ p₁ r′
... | inj₁ (p₂ , q₁ , q₂)                                       = r₂ ↯ nrf←nf p₂
... | inj₂ (_ , r₂′ , refl , refl)                              = app₂ & refl ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _ _) _} (app₂ (nf ()) r₂)  r′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₁ r₁′)     = app₁ & uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ r₁)          (app₂ p₁′ r₂′) = r₁ ↯ nrf←nf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₁ r₁′)     = r₁′ ↯ nrf←nf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)       (app₂ p₁′ r₂′) = app₂ & uniq-nf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-AO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (applam p₁ p₂)  (applam p₁′ p₂′) = refl
det-⇒ (applam p₁ p₂)  (app₁ (lam r₁′)) = r₁′ ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)  (app₂ p₁′ r₂′)   = r₂′ ↯ nrf←nf p₂
det-⇒ (lam r)         (lam r′)         = lam & refl ⊗ det-⇒ r r′
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
