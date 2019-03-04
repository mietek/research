---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep-AO where

open import Semantics-SmallStep
open AO public


---------------------------------------------------------------------------------------------------------------

open NonReducibleForms _⇒_ public

mutual
  nrf←nf : ∀ {n} {e : Tm n} → NF e → NRF e
  nrf←nf (lam p) = λ { (_ , lam r) → (_ , r) ↯ nrf←nf p }
  nrf←nf (nf p)  = nrf←nanf p

  nrf←nanf : ∀ {n} {e : Tm n} → NANF e → NRF e
  nrf←nanf var         = λ { (_ , ()) }
  nrf←nanf (app p₁ p₂) = λ { (_ , app₂ r₂)        → (_ , r₂) ↯ nrf←nf p₂
                            ; (_ , app₁ p₂′ r₁)    → (_ , r₁) ↯ nrf←nanf p₁
                            ; (_ , applam p₁′ p₂′) → case p₁ of λ ()
                            }

det-⇒ : ∀ {n} {e : Tm n} {e′ e″} → e ⇒ e′ → e ⇒ e″ → e′ ≡ e″
det-⇒ (lam r)            (lam r′)             = lam & det-⇒ r r′
det-⇒ (app₂ r₂)          (app₂ r₂′)           = app & refl ⊗ det-⇒ r₂ r₂′
det-⇒ (app₂ r₂)          (app₁ p₂′ r₁′)       = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₂ r₂)          (applam p₁′ p₂′)     = (_ , r₂) ↯ nrf←nf p₂′
det-⇒ (app₁ p₂ r₁)       (app₂ r₂′)           = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (app₁ p₂ r₁)       (app₁ p₂′ r₁′)       = app & det-⇒ r₁ r₁′ ⊗ refl
det-⇒ (app₁ p₂ (lam r₁)) (applam p₁′ p₂′)     = (_ , r₁) ↯ nrf←nf p₁′
det-⇒ (applam p₁ p₂)     (app₂ r₂′)           = (_ , r₂′) ↯ nrf←nf p₂
det-⇒ (applam p₁ p₂)     (app₁ p₂′ (lam r₁′)) = (_ , r₁′) ↯ nrf←nf p₁
det-⇒ (applam p₁ p₂)     (applam p₁′ p₂′)     = refl


---------------------------------------------------------------------------------------------------------------

open MultiStepReductions _⇒_ public
open Confluence _⇒_ det-⇒ public
open UniquenessOfNonReducibleForms _⇒_ det-⇒ public


---------------------------------------------------------------------------------------------------------------

nanf-⇒ : ∀ {n} {e : Tm n} {e′} → NANF e → e ⇒ e′ → NANF e′
nanf-⇒ var         ()
nanf-⇒ (app p₁ p₂) (app₂ r₂)        = (_ , r₂) ↯ nrf←nf p₂
nanf-⇒ (app p₁ p₂) (app₁ p₂′ r₁)    = app (nanf-⇒ p₁ r₁) p₂′
nanf-⇒ (app () p₂) (applam p₁′ p₂′)

nf-⇒ : ∀ {n} {e : Tm n} {e′} → NF e → e ⇒ e′ → NF e′
nf-⇒ (lam p) (lam r) = (_ , r) ↯ nrf←nf p
nf-⇒ (nf p)  r       = nf (nanf-⇒ p r)


---------------------------------------------------------------------------------------------------------------

lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
lam* = map lam

app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
app₂* = map app₂

app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NF e₂ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
app₁* p₁ = map (app₁ p₁)

applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₁ → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
applam* p₁ p₂ = applam p₁ p₂ ◅ ε


---------------------------------------------------------------------------------------------------------------

bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
bs-lam = lam*

bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
            e₁ ⇒* lam e₁′ → NF (lam e₁′) → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
            app e₁ e₂ ⇒* e′
bs-applam rs₁ (lam p₁′) rs₂ p₂′ rs = app₂* rs₂ ◅◅ app₁* p₂′ rs₁ ◅◅ applam* p₁′ p₂′ ◅◅ rs
bs-applam rs₁ (nf ())   rs₂ p₂′ rs

bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′} →
         e₁ ⇒* e₁′ → e₂ ⇒* e₂′ → NF e₂′ →
         app e₁ e₂ ⇒* app e₁′ e₂′
bs-app rs₁ rs₂ p₂′ = app₂* rs₂ ◅◅ app₁* p₂′ rs₁


---------------------------------------------------------------------------------------------------------------

rev-app₁-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               NF e₂ → app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × NF e₁′ × e₁′ [ e₂ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃ λ e₁′ → e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × app e₁′ e₂ ≡ e′)
rev-app₁-⇒* p₂ ε                    (nf (app p₁ p₂′)) = inj₂ (_ , ε , p₁ , refl)
rev-app₁-⇒* p₂ (app₂ r₂ ◅ rs)       p′ = (_ , r₂) ↯ nrf←nf p₂
rev-app₁-⇒* p₂ (app₁ p₂′ r₁ ◅ rs)   p′ with rev-app₁-⇒* p₂ rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs′)        = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)       = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , refl)
rev-app₁-⇒* p₂ (applam p₁ p₂′ ◅ rs) p′ = inj₁ (_ , ε , p₁ , rs)

rev-app₂-⇒* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → NF e′ →
               (∃² λ e₁′ e₂′ → e₁ ⇒*⟨ i ⟩ lam e₁′ × NF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ ×
                 e₁′ [ e₂′ ] ⇒*⟨ i ⟩ e′) ⊎
               (∃² λ e₁′ e₂′ → e₁ ⇒*⟨ i ⟩ e₁′ × NANF e₁′ × e₂ ⇒*⟨ i ⟩ e₂′ × NF e₂′ ×
                 app e₁′ e₂′ ≡ e′)
rev-app₂-⇒* ε                   (nf (app p₁ p₂)) = inj₂ (_ , ε , p₁ , ε , p₂ , refl)
rev-app₂-⇒* (app₂ r₂ ◅ rs)      p′               with rev-app₂-⇒* rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs₂ , p₂′ , rs′)      = inj₁ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , rs₂ , p₂′ , refl)     = inj₂ (_ , rs₁ , p₁′ , r₂ ◅ rs₂ , p₂′ , refl)
rev-app₂-⇒* (app₁ p₂ r₁ ◅ rs)   p′               with rev-app₁-⇒* p₂ rs p′
... | inj₁ (_ , rs₁ , p₁′ , rs′)                  = inj₁ (_ , r₁ ◅ rs₁ , p₁′ , ε , p₂ , rs′)
... | inj₂ (_ , rs₁ , p₁′ , refl)                 = inj₂ (_ , r₁ ◅ rs₁ , p₁′ , ε , p₂ , refl)
rev-app₂-⇒* (applam p₁ p₂ ◅ rs) p′               = inj₁ (_ , ε , p₁ , ε , p₂ , rs)

rev-lam-⇒* : ∀ {n i} {e : Tm (suc n)} {e′} →
              lam e ⇒*⟨ i ⟩ lam e′ → NF e′ →
              e ⇒*⟨ i ⟩ e′
rev-lam-⇒* ε            p′ = ε
rev-lam-⇒* (lam r ◅ rs) p′ with rev-lam-⇒* rs p′
... | rs′                   = r ◅ rs′


---------------------------------------------------------------------------------------------------------------

¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
¬lam⇒*var = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*var }

¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
¬lam⇒*app = λ { (lam r ◅ rs) → rs ↯ ¬lam⇒*app }


---------------------------------------------------------------------------------------------------------------
