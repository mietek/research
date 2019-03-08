---------------------------------------------------------------------------------------------------------------

module 1-3-Semantics-SmallStep where

open import 1-2-Syntax-Predicates public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-name reduction (Pierce)

module CBN where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {e₁ e₂} →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction (Pierce)
-- ∙ With corrected app₁ rule

module NO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    applam : ∀ {e₁ e₂} →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction, second stage (Garcia-Perez, et al.)

module NO₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam₋  : ∀ {e e′} →
            ¬ WHNF e → e CBN.⇒ e′ →
            lam e ⇒ lam e′

    lam₊  : ∀ {e e′} →
            WHNF e → e ⇒ e′ →
            lam e ⇒ lam e′

    app₁₊ : ∀ {e₁ e₂ e₁′} →
            NAXNF e₁ → e₁ ⇒ e₁′ →
            app e₁ e₂ ⇒ app e₁′ e₂

    app₂₋ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → ¬ WHNF e₂ → e₂ CBN.⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

    app₂₊ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → WHNF e₂ → e₂ ⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-value reduction (Pierce, modified)
-- ∙ With weak normal forms

module CBV where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {e₁ e₂} →
             WNF e₂ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             WNF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step applicative order reduction (no reference)

module AO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    applam : ∀ {e₁ e₂} →
             NF e₁ → NF e₂ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid applicative order reduction (no reference)

module HAO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam      : ∀ {e e′} →
               e ⇒ e′ →
               lam e ⇒ lam e′

    applam   : ∀ {e₁ e₂} →
               NF e₂ →
               app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    cbv-app₁ : ∀ {e₁ e₂ e₁′} →
               e₁ CBV.⇒ e₁′ →
               app e₁ e₂ ⇒ app e₁′ e₂

    app₁     : ∀ {e₁ e₂ e₁′} →
               NAWNF e₁ → e₁ ⇒ e₁′ →
               app e₁ e₂ ⇒ app e₁′ e₂

    app₂ₐ    : ∀ {e₁ e₂ e₂′} →
               e₂ ⇒ e₂′ →
               app (lam e₁) e₂ ⇒ app (lam e₁) e₂′

    app₂     : ∀ {e₁ e₂ e₂′} →
               NANF e₁ → e₂ ⇒ e₂′ →
               app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head spine reduction (no reference)

module HS where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    applam : ∀ {e₁ e₂} →
             HNF e₁ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head reduction (no reference)

module H where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    applam : ∀ {e₁ e₂} →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head reduction, second stage (no reference)

module H₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam₋   : ∀ {e e′} →
             ¬ WHNF e → e CBN.⇒ e′ →
             lam e ⇒ lam e′

    lam₊   : ∀ {e e′} →
             WHNF e → e ⇒ e′ →
             lam e ⇒ lam e′

    app₁₊  : ∀ {e₁ e₂ e₁′} →
             NAXNF e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid normal order reduction (no reference)

module HNO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    applam : ∀ {e₁ e₂} →
             HNF e₁ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁ₐ  : ∀ {e₁ e₁′ e₂} →
             ¬ HNF e₁ → e₁ ⇒ e₁′ →
             app (lam e₁) e₂ ⇒ app (lam e₁′) e₂

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid normal order reduction, second stage (no reference)

module HNO₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam₋  : ∀ {e e′} →
            ¬ HNF e → e HS.⇒ e′ →
            lam e ⇒ lam e′

    lam₊  : ∀ {e e′} →
            HNF e → e ⇒ e′ →
            lam e ⇒ lam e′

    app₁₊ : ∀ {e₁ e₂ e₁′} →
            NAXNF e₁ → e₁ ⇒ e₁′ →
            app e₁ e₂ ⇒ app e₁′ e₂

    app₂₋ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → ¬ HNF e₂ → e₂ HS.⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

    app₂₊ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → HNF e₂ → e₂ ⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

  open MultiStepReductions _⇒_ public


---------------------------------------------------------------------------------------------------------------
