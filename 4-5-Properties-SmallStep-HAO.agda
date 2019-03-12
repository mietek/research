---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HAO

module 4-5-Properties-SmallStep-HAO where

open import 2-2-Semantics-SmallStep
open HAO public
import 4-3-Properties-SmallStep-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-HAO reducible, NANF, or NF

-- TODO: Probably CBV needs something special

-- data Form : ∀ {n} → Pred₀ (Tm n) where
--   rf   : ∀ {n} {e : Tm n} → RF e → Form e
--   nanf : ∀ {n} {e : Tm n} → NANF e → Form e
--   nf   : ∀ {n} {e : Tm n} → ¬ NANF e → NF e → Form e
--
-- form? : ∀ {n} (e : Tm n) → Form e
-- form? (var x)                             = nanf var
-- form? (lam e)                             with form? e
-- ... | rf (_ , r)                          = rf (_ , lam r)
-- ... | nanf p                              = nf (λ ()) (lam (nf p))
-- ... | nf _ p                              = nf (λ ()) (lam p)
-- form? (app e₁ ●₂)                         with form? e₁ | form? ●₂
-- ... | rf (_ , lam r₁)      | rf (_ , r₂)  = rf (_ , app₂ₐ r₂)
-- ... | rf (_ , lam r₁)      | nanf p₂      = rf (_ , applam (nf p₂))
-- ... | rf (_ , lam r₁)      | nf _ p₂      = rf (_ , applam p₂)
-- ... | rf (_ , applam p₂)   | rf (_ , r₂)  = rf (_ , app₂ (app {!!} p₂) r₂)
-- ... | rf (_ , applam p₂)   | nanf p₂′     = nanf (app (app {!!} p₂) (nf p₂′))
-- ... | rf (_ , applam p₂)   | nf _ p₂′     = nanf (app (app {!!} p₂) p₂′)
-- ... | rf (_ , cbv-app₁ r₁) | f₂           = rf (_ , cbv-app₁ (CBV.app₁ r₁))
-- ... | rf (_ , app₁ p₁ r₁)  | rf (_ , r₂)  = rf (_ , app₂ (app {!!} {!!}) r₂)
-- ... | rf (_ , app₁ p₁ r₁)  | nanf p₂      = {!!}
-- ... | rf (_ , app₁ p₁ r₁)  | nf _ p₂      = {!!}
-- ... | rf (_ , app₂ₐ r₂)    | rf (_ , r₂′) = {!!}
-- ... | rf (_ , app₂ₐ r₂)    | nanf p₂      = {!!}
-- ... | rf (_ , app₂ₐ r₂)    | nf _ p₂      = {!!}
-- ... | rf (_ , app₂ p₁ r₂)  | rf (_ , r₂′) = {!!}
-- ... | rf (_ , app₂ p₁ r₂)  | nanf p₂      = {!!}
-- ... | rf (_ , app₂ p₁ r₂)  | nf _ p₂      = {!!}
-- ... | nanf p₁              | rf (_ , r₂)  = rf (_ , app₂ p₁ r₂)
-- ... | nanf p₁              | nanf p₂      = nanf (app p₁ (nf p₂))
-- ... | nanf p₁              | nf _ p₂      = nanf (app p₁ p₂)
-- ... | nf _ (lam p₁)        | rf (_ , r₂)  = rf (_ , app₂ₐ r₂)
-- ... | nf _ (lam p₁)        | nanf p₂      = rf (_ , applam (nf p₂))
-- ... | nf _ (lam p₁)        | nf _ p₂      = rf (_ , applam p₂)
-- ... | nf ¬p₁ (nf p₁)       | _            = p₁ ↯ ¬p₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO does not reduce NF

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (lam r) → r ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ ()
  nrf←nanf (app p₁ p₂) = λ { (applam p₂′)  → case p₁ of λ ()
                            ; (cbv-app₁ r₁) → r₁ ↯ CBV.nrf←wnf (wnf←nf (nf p₁))
                            ; (app₁ p₁′ r₁) → r₁ ↯ nrf←nanf p₁
                            ; (app₂ₐ r₂)    → r₂ ↯ nrf←nf p₂
                            ; (app₂ p₁′ r₂) → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₂ : NF e₂) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₂ })
rev-applam p₂ (applam p₂′)  = refl , applam & uniq-nf p₂′ p₂
rev-applam p₂ (cbv-app₁ ())
rev-applam p₂ (app₁ () r₁)
rev-applam p₂ (app₂ₐ r₂)    = r₂ ↯ nrf←nf p₂
rev-applam p₂ (app₂ p₁ r₂)  = r₂ ↯ nrf←nf p₂

rev-app₂ₐ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
            (r : app (lam e₁) e₂ ⇒ e′) →
            (∃ λ p₂ →
              Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
                r ≡ applam p₂ }) ⊎
            (Σ {_} {0ᴸ} (Tm n) λ e₂′ →
              Σ (e₂ ⇒ e₂′) λ r₂ →
                Σ (e′ ≡ app (lam e₁) e₂′) λ { refl →
                  r ≡ app₂ₐ r₂ })
rev-app₂ₐ (applam p₂)   = inj₁ (p₂ , refl , refl)
rev-app₂ₐ (cbv-app₁ ())
rev-app₂ₐ (app₁ () r₁)
rev-app₂ₐ (app₂ₐ r₂)    = inj₂ (_ , r₂ , refl , refl)
rev-app₂ₐ (app₂ () r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()            ()
uniq-⇒ {e = lam _}           (lam r)       (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (cbv-app₁ ()) r′
uniq-⇒ {e = app (var _) _}   (app₁ p₁ ())  r′
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)  (cbv-app₁ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)  (app₁ p₁′ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)  (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (applam p₂)   r′             with rev-applam p₂ r′
... | refl , refl                                          = refl
uniq-⇒ {e = app (lam _) _}   (cbv-app₁ ()) r′
uniq-⇒ {e = app (lam _) _}   (app₁ () r₁)  r′
uniq-⇒ {e = app (lam _) _}   (app₂ₐ r₂)    r′             with rev-app₂ₐ r′
... | inj₁ (p₂ , q₁ , q₂)                                  = r₂ ↯ nrf←nf p₂
... | inj₂ (_ , r₂′ , refl , refl)                         = app₂ₐ & uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (app₂ () r₂) r′
uniq-⇒ {e = app (app _ _) _} (cbv-app₁ r₂) (cbv-app₁ r₂′) = cbv-app₁ & CBV.uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (app _ _) _} (cbv-app₁ r₂) (app₁ p₁′ r₁′) = r₂ ↯ CBV.nrf←nawnf p₁′
uniq-⇒ {e = app (app _ _) _} (cbv-app₁ r₂) (app₂ p₁′ r₂′) = r₂ ↯ CBV.nrf←wnf (wnf←nf (nf p₁′))
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)  (cbv-app₁ r₂′) = r₂′ ↯ CBV.nrf←nawnf p₁
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)  (app₁ p₁′ r₁′) = app₁ & uniq-nawnf p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)  (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)  (cbv-app₁ r₂′) = r₂′ ↯ CBV.nrf←wnf (wnf←nf (nf p₁))
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)  (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)  (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)       (lam r′)       = lam & det-⇒ r r′
det-⇒ (applam p₂)   (applam p₂′)   = refl
det-⇒ (applam p₂)   (cbv-app₁ ())
det-⇒ (applam p₂)   (app₁ () r₁′)
det-⇒ (applam p₂)   (app₂ₐ r₂′)    = r₂′ ↯ nrf←nf p₂
det-⇒ (applam p₂)   (app₂ p₁′ r₂′) = r₂′ ↯ nrf←nf p₂
det-⇒ (cbv-app₁ ()) (applam p₂′)
det-⇒ (cbv-app₁ r₁) (cbv-app₁ r₁′) = app & CBV.det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (cbv-app₁ r₁) (app₁ p₁′ r₁′) = r₁ ↯ CBV.nrf←nawnf p₁′
det-⇒ (cbv-app₁ ()) (app₂ₐ r₂′)
det-⇒ (cbv-app₁ r₁) (app₂ p₁′ r₂′) = r₁ ↯ CBV.nrf←nawnf (nawnf←nanf p₁′)
det-⇒ (app₁ () r₁)  (applam p₂′)
det-⇒ (app₁ p₁ r₁)  (cbv-app₁ r₁′) = r₁′ ↯ CBV.nrf←nawnf p₁
det-⇒ (app₁ p₁ r₁)  (app₁ p₁′ r₁′) = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ () r₁)  (app₂ₐ r₂′)
det-⇒ (app₁ p₁ r₁)  (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₂ p₁ r₂)  (applam p₂′)   = r₂ ↯ nrf←nf p₂′
det-⇒ (app₂ p₁ r₂)  (cbv-app₁ r₁′) = r₁′ ↯ CBV.nrf←nawnf (nawnf←nanf p₁)
det-⇒ (app₂ p₁ r₂)  (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂ () r₂)  (app₂ₐ r₂′)
det-⇒ (app₂ p₁ r₂)  (app₂ p₁′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂ₐ r₂)    (applam p₂′)   = r₂ ↯ nrf←nf p₂′
det-⇒ (app₂ₐ r₂)    (cbv-app₁ ())
det-⇒ (app₂ₐ r₂)    (app₁ () r₁′)
det-⇒ (app₂ₐ r₂)    (app₂ₐ r₂′)    = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂ₐ r₂)    (app₂ () r₂′)

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO preserves WNF

mutual
  wnf-⇒ : ∀ {n} {e : Tm n} {e′} → WNF e → e ⇒ e′ → WNF e′
  wnf-⇒ lam     (lam r) = lam
  wnf-⇒ (wnf p) r       = wnf (nawnf-⇒ p r)

  nawnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇒ e′ → NAWNF e′
  nawnf-⇒ var         ()
  nawnf-⇒ (app () p₂) (applam p₂′)
  nawnf-⇒ (app p₁ p₂) (cbv-app₁ r₁) = r₁ ↯ CBV.nrf←nawnf p₁
  nawnf-⇒ (app p₁ p₂) (app₁ p₁′ r₁) = app (nawnf-⇒ p₁′ r₁) p₂
  nawnf-⇒ (app () p₂) (app₂ₐ r₂)
  nawnf-⇒ (app p₁ p₂) (app₂ p₁′ r₂) = app p₁ (wnf-⇒ p₂ r₂)


---------------------------------------------------------------------------------------------------------------
