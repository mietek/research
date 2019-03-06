---------------------------------------------------------------------------------------------------------------
--
-- Properties of SS-HAO

module 2-5-1-Properties-SmallStep-HAO where

open import 1-3-Semantics-SmallStep
open HAO public
import 2-3-Properties-SmallStep-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO contains SS-CBV

hao←cbv : ∀ {n} {e : Tm n} {e′} → e CBV.⇒ e′ → e ⇒ e′
hao←cbv (CBV.applam p₂)  = applam p₂
hao←cbv (CBV.app₁ r₁)    with wnf? _
... | no ¬p₁              = app₁₋ ¬p₁ (hao←cbv r₁)
... | yes p₁              = (_ , r₁) ↯ CBV.nrf←wnf p₁
hao←cbv (CBV.app₂ p₁ r₂) with wnf? _
... | no ¬p₂              = app₂₋ p₁ ¬p₂ (hao←cbv r₂)
... | yes p₂              = (_ , r₂) ↯ CBV.nrf←wnf p₂


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO does not reduce NF

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p
                      }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , applam p₂′)        → case p₁ of λ ()
                            ; (_ , app₁₋ ¬p₁′ r₁)     → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₁₊ p₁′ p₂′ r₁)  → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , app₂₋ p₁′ ¬p₂′ r₂) → (_ , r₂) ↯ nrf←nf p₂
                            ; (_ , app₂₊ p₁′ r₂)      → (_ , r₂) ↯ nrf←nf p₂
                            }


---------------------------------------------------------------------------------------------------------------
--
-- SS-HAO is deterministic, confluent, and has unique non-reducible forms

det-⇒ : Deterministic _⇒_
det-⇒ (lam r)           (lam r′)             = lam & det-⇒ r r′
det-⇒ (applam p₂)       (applam p₂′)         = refl
det-⇒ (applam p₂)       (app₁₋ ¬p₁′ r₁′)     = lam ↯ ¬p₁′
det-⇒ (applam p₂)       (app₁₊ () p₂′ r₁′)
det-⇒ (applam p₂)       (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (applam p₂)       (app₂₊ () r₂′)
det-⇒ (app₁₋ ¬p₁ r₁)    (applam p₂′)         = lam ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁)    (app₁₋ ¬p₁′ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₋ ¬p₁ r₁)    (app₁₊ p₁′ p₂′ r₁′)  = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₋ ¬p₁ r₁)    (app₂₋ p₁′ ¬p₂′ r₂′) = p₁′ ↯ ¬p₁
det-⇒ (app₁₋ ¬p₁ r₁)    (app₂₊ p₁′ r₂′)      = wnf←nf (nf p₁′) ↯ ¬p₁
det-⇒ (app₁₊ () p₂ r₁)  (applam p₂′)
det-⇒ (app₁₊ p₁ p₂ r₁)  (app₁₋ ¬p₁′ r₁′)     = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ p₂ r₁)  (app₁₊ p₁′ p₂′ r₁′)  = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁₊ p₁ p₂ r₁)  (app₂₋ p₁′ ¬p₂′ r₂′) = p₂ ↯ ¬p₂′
det-⇒ (app₁₊ p₁ p₂ r₁)  (app₂₊ p₁′ r₂′)      = (_ , r₁) ↯ nrf←nanf p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (applam p₂′)         = p₂′ ↯ ¬p₂
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₋ ¬p₁′ r₁′)     = p₁ ↯ ¬p₁′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₁₊ p₁′ p₂′ r₁′)  = p₂′ ↯ ¬p₂
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂₋ p₁ ¬p₂ r₂) (app₂₊ p₁′ r₂′)      = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂₊ () r₂)     (applam p₂′)
det-⇒ (app₂₊ p₁ r₂)     (app₁₋ ¬p₁′ r₁′)     = wnf←nf (nf p₁) ↯ ¬p₁′
det-⇒ (app₂₊ p₁ r₂)     (app₁₊ p₁′ p₂′ r₁′)  = (_ , r₁′) ↯ nrf←nanf p₁
det-⇒ (app₂₊ p₁ r₂)     (app₂₋ p₁′ ¬p₂′ r₂′) = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂₊ p₁ r₂)     (app₂₊ p₁′ r₂′)      = app & refl ⊗ det-⇒ r₂ r₂′

open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


-- -- -- -- ---------------------------------------------------------------------------------------------------------------
-- -- -- -- --
-- -- -- -- -- SS-HAO preserves NF and WNF

-- -- -- -- nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
-- -- -- -- nanf-⇒ var         ()
-- -- -- -- nanf-⇒ (app () p₂) (applam p₂′)
-- -- -- -- nanf-⇒ (app p₁ p₂) (app₁ p₁′ r₁ p₂′) = app (nanf-⇒ p₁ r₁) p₂′
-- -- -- -- nanf-⇒ (app p₁ p₂) (app₂ r₂)         = (_ , r₂) ↯ nrf←nf p₂

-- -- -- -- nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
-- -- -- -- nf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←nf p
-- -- -- -- nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)

-- -- -- -- mutual
-- -- -- --   wnf-⇒ : ∀ {n} {e : Tm n} {e′} → WNF e → e ⇒ e′ → WNF e′
-- -- -- --   wnf-⇒ lam     (lam r) = lam
-- -- -- --   wnf-⇒ (wnf p) r       = wnf (nawnf-⇒ p r)

-- -- -- --   nawnf-⇒ : ∀ {n} {e : Tm n} {e′} → NAWNF e → e ⇒ e′ → NAWNF e′
-- -- -- --   nawnf-⇒ var         ()
-- -- -- --   nawnf-⇒ (app () p₂) (applam p₂′)
-- -- -- --   nawnf-⇒ (app p₁ p₂) (app₁ p₁′ r₁ p₂′) = app (nawnf-⇒ p₁ r₁) p₂
-- -- -- --   nawnf-⇒ (app p₁ p₂) (app₂ r₂)         = app p₁ (wnf-⇒ p₂ r₂)


-- -- -- -- ---------------------------------------------------------------------------------------------------------------
