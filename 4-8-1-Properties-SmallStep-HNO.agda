---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HNO

module 4-8-1-Properties-SmallStep-HNO where

open import 2-2-Semantics-SmallStep
open HNO public
import 4-6-Properties-SmallStep-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO contains SS-HS

mutual
  hs-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ HS.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
  hs-app₁ (HS.applam p₁) = app₁ app (applam p₁)
  hs-app₁ (HS.lam r)     = app₁ₐ (HS.rev-¬hnf-⇒ r) (hno←hs r)
  hs-app₁ (HS.app₁ r₁)   = app₁ app (hs-app₁ r₁)

  hno←hs : ∀ {n} {e : Tm n} {e′} → e HS.⇒ e′ → e ⇒ e′
  hno←hs (HS.applam p₁) = applam p₁
  hno←hs (HS.lam r)     = lam (hno←hs r)
  hno←hs (HS.app₁ r₁)   = hs-app₁ r₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO contains SS-HNO₂

hno←hno₂ : ∀ {n} {e : Tm n} {e′} → e HNO₂.⇒ e′ → e ⇒ e′
hno←hno₂ (HNO₂.lam p r)           = lam (hno←hno₂ r)
hno←hno₂ (HNO₂.app₁ p₁ r₁)        = app₁ (na←naxnf p₁) (hno←hno₂ r₁)
hno←hno₂ (HNO₂.hs-app₂ p₁ ¬p₂ r₂) = app₂ p₁ (hno←hs r₂)
hno←hno₂ (HNO₂.app₂ p₁ p₂ r₂)     = app₂ p₁ (hno←hno₂ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- Every term is either SS-HNO-reducible or NF

data RF? {n} : Pred₀ (Tm n) where
  yes : ∀ {e} → RF e → RF? e
  no  : ∀ {e} → NF e → RF? e

rf? : ∀ {n} (e : Tm n) → RF? e
rf? (var x)                                                    = no (nf var)
rf? (lam e)                                                    with rf? e
... | yes (_ , r)                                              = yes (_ , lam r)
... | no p                                                     = no (lam p)
rf? (app e₁ e₂)                                                with rf? e₁ | rf? e₂
rf? (app e₁ e₂) | yes (_ , applam p₁)   | _                    = yes (_ , app₁ app (applam p₁))
rf? (app e₁ e₂) | yes (_ , lam r₁)      | _                    with hnf? _
rf? (app e₁ e₂) | yes (_ , lam r₁)      | _            | yes p = yes (_ , applam p)
rf? (app e₁ e₂) | yes (_ , lam r₁)      | _            | no ¬p = yes (_ , app₁ₐ ¬p r₁)
rf? (app e₁ e₂) | yes (_ , app₁ₐ p₁ r₁) | _                    = yes (_ , app₁ app (app₁ₐ p₁ r₁))
rf? (app e₁ e₂) | yes (_ , app₁ p₁ r₁)  | _                    = yes (_ , app₁ app (app₁ p₁ r₁))
rf? (app e₁ e₂) | yes (_ , app₂ p₁ r₂)  | _                    = yes (_ , app₁ app (app₂ p₁ r₂))
rf? (app e₁ e₂) | no (lam p₁)           | _                    = yes (_ , applam (hnf←nf p₁))
rf? (app e₁ e₂) | no (nf p₁)            | yes (_ , r₂)         = yes (_ , app₂ p₁ r₂)
rf? (app e₁ e₂) | no (nf p₁)            | no p₂                = no (nf (app p₁ p₂))


---------------------------------------------------------------------------------------------------------------
--
-- Every term has a potentially-infinite sequence of SS-HNO reductions that may terminate at a NF

eval : ∀ {n i} (e : Tm n) → e ᶜᵒ⇓[ NF ]⟨ i ⟩
eval e            with rf? e
... | yes (_ , r) = r ◅ λ where .force → eval _
... | no p        = ε p


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO does not reduce NF

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
  nrf←nanf (app p₁ p₂) = λ { (applam p₁′)   → case p₁ of λ ()
                            ; (app₁ₐ ¬p₁ r₁) → case p₁ of λ ()
                            ; (app₁ p₁′ r₁)  → r₁ ↯ nrf←nanf p₁
                            ; (app₂ p₁′ r₂)  → r₂ ↯ nrf←nf p₂ }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO is unique

rev-applam : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
             (p₁ : HNF e₁) (r : app (lam e₁) e₂ ⇒ e′) →
             (Σ (e′ ≡ e₁ [ e₂ ]) λ { refl →
               r ≡ applam p₁ })
rev-applam p₁ (applam p₁′)   = refl , applam & uniq-hnf p₁′ p₁
rev-applam p₁ (app₁ₐ ¬p₁ r₁) = p₁ ↯ ¬p₁
rev-applam p₁ (app₁ () r₁)
rev-applam p₁ (app₂ () r₂)

rev-app₁ₐ : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e′} →
            (¬p₁ : ¬ HNF e₁) (r : app (lam e₁) e₂ ⇒ e′) →
            (Σ {_} {0ᴸ} (Tm (suc n)) λ e₁′ →
              Σ (e₁ ⇒ e₁′) λ r₁ →
                Σ (e′ ≡ app (lam e₁′) e₂) λ { refl →
                  r ≡ app₁ₐ ¬p₁ r₁ })
rev-app₁ₐ ¬p₁ (applam p₁)     = p₁ ↯ ¬p₁
rev-app₁ₐ ¬p₁ (app₁ₐ ¬p₁′ r₁) = _ , r₁ , refl , app₁ₐ & uniq-¬hnf ¬p₁′ ¬p₁ ⊗ refl
rev-app₁ₐ ¬p₁ (app₁ () r₁)
rev-app₁ₐ ¬p₁ (app₂ () r₂)

uniq-⇒ : Unique _⇒_
uniq-⇒ {e = var _}           ()             ()
uniq-⇒ {e = lam _}           (lam r)        (lam r′)       = lam & uniq-⇒ r r′
uniq-⇒ {e = app (var _) _}   (app₁ p₁ ())   r′
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)   (app₁ p₁′ ())
uniq-⇒ {e = app (var _) _}   (app₂ p₁ r₂)   (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′
uniq-⇒ {e = app (lam _) _}   (applam p₁)    r′             with rev-applam p₁ r′
... | refl , refl                                           = refl
uniq-⇒ {e = app (lam _) _}   (app₁ₐ ¬p₁ r₁) r′             with rev-app₁ₐ ¬p₁ r′
... | _ , r₁′ , refl , refl                                 = app₁ₐ & refl ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (lam _) _}   (app₁ () r₁)   r′
uniq-⇒ {e = app (lam _) _}   (app₂ () r₂)   r′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)   (app₁ p₁′ r₁′) = app₁ & uniq-na p₁ p₁′ ⊗ uniq-⇒ r₁ r₁′
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)   (app₂ p₁′ r₂′) = r₁ ↯ nrf←nanf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)   (app₁ p₁′ r₁′) = r₁′ ↯ nrf←nanf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)   (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO is deterministic, confluent, and gives rise to deterministic evaluation to NRF

det-⇒ : Deterministic _⇒_
det-⇒ (applam p₁)    (applam p₁′)     = refl
det-⇒ (applam p₁)    (app₁ₐ ¬p₁′ r₁′) = p₁ ↯ ¬p₁′
det-⇒ (applam p₁)    (app₁ () r₁′)
det-⇒ (applam p₁)    (app₂ () r₂′)
det-⇒ (lam r)        (lam r′)         = lam & det-⇒ r r′
det-⇒ (app₁ₐ ¬p₁ r₁) (applam p₁′)     = p₁′ ↯ ¬p₁
det-⇒ (app₁ₐ ¬p₁ r₁) (app₁ₐ ¬p₁′ r₁′) = app & (lam & det-⇒ r₁ r₁′) ⊗ refl
det-⇒ (app₁ₐ ¬p₁ r₁) (app₁ () r₁′)
det-⇒ (app₁ₐ ¬p₁ r₁) (app₂ () r₂′)
det-⇒ (app₁ () r₁)   (applam p₁′)
det-⇒ (app₁ () r₁)   (app₁ₐ ¬p₁′ r₁′)
det-⇒ (app₁ p₁ r₁)   (app₁ p₁′ r₁′)   = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁)   (app₂ p₁′ r₂′)   = r₁ ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂)   (applam p₁′)
det-⇒ (app₂ () r₂)   (app₁ₐ ¬p₁′ r₁′)
det-⇒ (app₂ p₁ r₂)   (app₁ p₁′ r₁′)   = r₁′ ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂)   (app₂ p₁′ r₂′)   = app & refl ⊗ det-⇒ r₂ r₂′

conf-⇒ : Confluent _⇒_
conf-⇒ = cor-conf-⇒ det-⇒

det-⇓-nrf : Deterministic _⇓[ NRF ]_
det-⇓-nrf = cor-det-⇓-nrf det-⇒


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO preserves HNF

naxnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇒ e′ → NAXNF e′
naxnf-⇒ var      ()
naxnf-⇒ (app ()) (applam p₁′)
naxnf-⇒ (app ()) (app₁ₐ ¬p₁′ r₁)
naxnf-⇒ (app p₁) (app₁ p₁′ r₁)   = app (naxnf-⇒ p₁ r₁)
naxnf-⇒ (app p₁) (app₂ p₁′ r₂)   = app p₁

hnf-⇒ : ∀ {n} {e : Tm n} {e′} → HNF e → e ⇒ e′ → HNF e′
hnf-⇒ (lam p) (lam r) = lam (hnf-⇒ p r)
hnf-⇒ (hnf p) r       = hnf (naxnf-⇒ p r)


---------------------------------------------------------------------------------------------------------------
