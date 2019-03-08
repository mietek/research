---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HNO

module 2-8-1-Properties-SmallStep-HNO where

open import 1-3-Semantics-SmallStep
open HNO public
import 2-6-Properties-SmallStep-HS as SS-HS


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO contains SS-HS

mutual
  hs-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ HS.⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
  hs-app₁ (HS.applam p₁) = app₁ app (applam p₁)
  hs-app₁ (HS.lam r)     = app₁ₐ (λ p → (_ , r) ↯ SS-HS.nrf←hnf p) (hno←hs r)
  hs-app₁ (HS.app₁ r₁)   = app₁ app (hs-app₁ r₁)

  hno←hs : ∀ {n} {e : Tm n} {e′} → e HS.⇒ e′ → e ⇒ e′
  hno←hs (HS.applam p₁) = applam p₁
  hno←hs (HS.lam r)     = lam (hno←hs r)
  hno←hs (HS.app₁ r₁)   = hs-app₁ r₁


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO contains SS-HNO₂

app₁₊ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒ e₁′ → app e₁ e₂ ⇒ app e₁′ e₂
app₁₊ var      r₁ = app₁ var r₁
app₁₊ (app p₁) r₁ = app₁ app r₁

hno←hno₂ : ∀ {n} {e : Tm n} {e′} → e HNO₂.⇒ e′ → e ⇒ e′
hno←hno₂ (HNO₂.lam₋ ¬p r)       = lam (hno←hs r)
hno←hno₂ (HNO₂.lam₊ p r)        = lam (hno←hno₂ r)
hno←hno₂ (HNO₂.app₁₊ p₁ r₁)     = app₁₊ p₁ (hno←hno₂ r₁)
hno←hno₂ (HNO₂.app₂₋ p₁ ¬p₂ r₂) = app₂ p₁ (hno←hs r₂)
hno←hno₂ (HNO₂.app₂₊ p₁ p₂ r₂)  = app₂ p₁ (hno←hno₂ r₂)


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam p₁′)   → case p₁ of λ ()
                            ; (_ , app₁ₐ ¬p₁ r₁) → case p₁ of λ ()
                            ; (_ , app₁ p₁′ r₁)  → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂ p₁′ r₂)  → (_ , r₂) ↯ nrf←nf p₂
                            }


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

uniq-⇒ : Unique² _⇒_
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
uniq-⇒ {e = app (app _ _) _} (app₁ p₁ r₁)   (app₂ p₁′ r₂′) = (_ , r₁) ↯ nrf←nanf p₁′
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)   (app₁ p₁′ r₁′) = (_ , r₁′) ↯ nrf←nanf p₁
uniq-⇒ {e = app (app _ _) _} (app₂ p₁ r₂)   (app₂ p₁′ r₂′) = app₂ & uniq-nanf p₁ p₁′ ⊗ uniq-⇒ r₂ r₂′


---------------------------------------------------------------------------------------------------------------
--
-- SS-HNO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)        (lam r′)         = lam & det-⇒ r r′
det-⇒ (applam p₁)    (applam p₁′)     = refl
det-⇒ (applam p₁)    (app₁ₐ ¬p₁′ r₁′) = p₁ ↯ ¬p₁′
det-⇒ (applam p₁)    (app₁ () r₁′)
det-⇒ (applam p₁)    (app₂ () r₂′)
det-⇒ (app₁ₐ ¬p₁ r₁) (applam p₁′)     = p₁′ ↯ ¬p₁
det-⇒ (app₁ₐ ¬p₁ r₁) (app₁ₐ ¬p₁′ r₁′) = app & (lam & det-⇒ r₁ r₁′) ⊗ refl
det-⇒ (app₁ₐ ¬p₁ r₁) (app₁ () r₁′)
det-⇒ (app₁ₐ ¬p₁ r₁) (app₂ () r₂′)
det-⇒ (app₁ () r₁)   (applam p₁′)
det-⇒ (app₁ () r₁)   (app₁ₐ ¬p₁′ r₁′)
det-⇒ (app₁ p₁ r₁)   (app₁ p₁′ r₁′)   = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₁ r₁)   (app₂ p₁′ r₂′)   = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂ () r₂)   (applam p₁′)
det-⇒ (app₂ () r₂)   (app₁ₐ ¬p₁′ r₁′)
det-⇒ (app₂ p₁ r₂)   (app₁ p₁′ r₁′)   = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂ p₁ r₂)   (app₂ p₁′ r₂′)   = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


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
