---------------------------------------------------------------------------------------------------------------
--
-- Generic equipment for well-scoped terms

open import 0-1-Prelude

module 0-2-GenericEquipment (Tm : Nat → Set) where


---------------------------------------------------------------------------------------------------------------
--
-- Properties of relations on well-scoped terms

module Unary where
  Decidable : Pred (∀ {n} → Pred₀ (Tm n)) _
  Decidable P = ∀ {n} → Relations.Unary.Decidable (P {n})

  Unique : Pred (∀ {n} → Pred₀ (Tm n)) _
  Unique P = ∀ {n} → Relations.Unary.Unique (P {n})

module Binary where
  Unique : Pred (∀ {n} → Rel₀ (Tm n)) _
  Unique R = ∀ {n} → Relations.Binary.Unique (R {n})

  Deterministic : Pred (∀ {n} → Rel₀ (Tm n)) _
  Deterministic R = ∀ {n} → Relations.Binary.Deterministic (R {n})

  Confluent : Pred (∀ {n} → Rel₀ (Tm n)) _
  Confluent R = ∀ {n} → Relations.Binary.Confluent (R {n})


---------------------------------------------------------------------------------------------------------------
--
-- Equipment derived from small-step reduction on well-scoped terms

module DerivedEquipment (_⇒_ : ∀ {n} → Rel₀ (Tm n)) where
  -- Reducible forms
  RF : ∀ {n} → Pred₀ (Tm n)
  RF e = ∃ λ e′ → e ⇒ e′

  -- Universal non-reducible forms
  NRF : ∀ {n} → Pred₀ (Tm n)
  NRF e = ∀ {e′} → ¬ (e ⇒ e′)

  ¬rf←nrf : ∀ {n} {e : Tm n} → NRF e → ¬ RF e
  ¬rf←nrf p = λ { (_ , r) → r ↯ p }

  nrf←¬rf : ∀ {n} {e : Tm n} → ¬ RF e → NRF e
  nrf←¬rf p = λ r → (_ , r) ↯ p

  -- Iterated small-step reduction, indexed by size
  _⇒*⟨_⟩_ : ∀ {n} → Tm n → Size → Tm n → Set
  e ⇒*⟨ i ⟩ e′ = (_⇒_ *⟨ i ⟩) e e′

  -- Iterated small-step reduction
  _⇒*_ : ∀ {n} → Rel₀ (Tm n)
  e ⇒* e′ = e ⇒*⟨ ∞ ⟩ e′

  -- Evaluation, indexed by value predicate and size
  _⇓[_]⟨_⟩_ : ∀ {n} → Tm n → (∀ {n} → Pred₀ (Tm n)) → Size → Tm n → Set
  e ⇓[ P ]⟨ i ⟩ e′ = e ⇒*⟨ i ⟩ e′ × P e′

  -- Evaluation, indexed by value predicate
  _⇓[_]_ : ∀ {n} → Tm n → (∀ {n} → Pred₀ (Tm n)) → Tm n → Set
  e ⇓[ P ] e′ = e ⇓[ P ]⟨ ∞ ⟩ e′

  -- Termination, indexed by value predicate and size
  _⇓[_]⟨_⟩ : ∀ {n} → Tm n → (∀ {n} → Pred₀ (Tm n)) → Size → Set
  e ⇓[ P ]⟨ i ⟩ = ∃ λ e′ → e ⇓[ P ]⟨ i ⟩ e′

  -- Termination, indexed by value predicate
  _⇓[_] : ∀ {n} → Tm n → (∀ {n} → Pred₀ (Tm n)) → Set
  e ⇓[ P ] = e ⇓[ P ]⟨ ∞ ⟩

  {-# DISPLAY _*⟨_⟩ _⇒_ i e e′   = e ⇒*⟨ i ⟩ e′ #-}
  {-# DISPLAY _*⟨_⟩ _⇒_ ∞ e e′   = e ⇒* e′ #-}
  {-# DISPLAY _* _⇒_ e e′        = e ⇒* e′ #-}
  {-# DISPLAY _⇓[_]⟨_⟩_ e P ∞ e′  = e ⇓[ P ] e′ #-}
  {-# DISPLAY _⇓[_]⟨_⟩ e P ∞      = e ⇓[ P ] #-}

  -- Coinductive evaluation/potential termination, indexed by value predicate and size
  data _ᶜᵒ⇓[_]⟨_⟩ : ∀ {n} → Tm n → (∀ {n} → Pred₀ (Tm n)) → Size → Set where
    ε   : ∀ {n i} {P : ∀ {n} → Pred₀ (Tm n)} {e : Tm n} →
          P e →
          e ᶜᵒ⇓[ P ]⟨ i ⟩

    _◅_ : ∀ {n i} {P : ∀ {n} → Pred₀ (Tm n)} {e : Tm n} {e′} →
          e ⇒ e′ → Thunk (e′ ᶜᵒ⇓[ P ]⟨_⟩) i →
          e ᶜᵒ⇓[ P ]⟨ i ⟩

  trace : ∀ {n i} {P : ∀ {n} → Pred₀ (Tm n)} {e : Tm n} → e ᶜᵒ⇓[ P ]⟨ i ⟩ → Colist (Tm n) i
  trace (ε {e = e} p)      = e ∷ λ where .force → []
  trace (_◅_ {e = e} r rs) = e ∷ λ where .force → trace (rs .force)

  -- Confluence of small-step reduction, as a corollary of determinism of small-step reduction
  cor-conf-⇒ : Binary.Deterministic _⇒_ → Binary.Confluent _⇒_
  cor-conf-⇒ det ε        rs′        = _ , rs′ , ε
  cor-conf-⇒ det (r ◅ rs) ε          = _ , ε , r ◅ rs
  cor-conf-⇒ det (r ◅ rs) (r′ ◅ rs′) with det r r′
  ... | refl                          = cor-conf-⇒ det rs rs′

  -- Determinism of evaluation to NRF, as a corollary of determinism of small-step reduction
  cor-det-⇓-nrf : Binary.Deterministic _⇒_ → Binary.Deterministic _⇓[ NRF ]_
  cor-det-⇓-nrf det (ε        , p) (ε          , p′) = refl
  cor-det-⇓-nrf det (ε        , p) ((r′ ◅ rs′) , p′) = r′ ↯ p
  cor-det-⇓-nrf det ((r ◅ rs) , p) (ε          , p′) = r ↯ p′
  cor-det-⇓-nrf det ((r ◅ rs) , p) ((r′ ◅ rs′) , p′) with det r r′
  ... | refl                                         = cor-det-⇓-nrf det (rs , p) (rs′ , p′)


---------------------------------------------------------------------------------------------------------------
