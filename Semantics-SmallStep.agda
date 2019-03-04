---------------------------------------------------------------------------------------------------------------

module Semantics-SmallStep where

open import Syntax-Predicates public


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


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction, post-CBN fragment (Garcia-Perez, et al.)

module NO₊ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    app₁₊ : ∀ {e₁ e₂ e₁′} →
            NAXNF e₁ → e₁ ⇒ e₁′ →
            app e₁ e₂ ⇒ app e₁′ e₂

    app₂₋ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → ¬ WHNF e₂ → e₂ CBN.⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

    app₂₊ : ∀ {e₁ e₂ e₂′} →
            NANF e₁ → WHNF e₂ → e₂ ⇒ e₂′ →
            app e₁ e₂ ⇒ app e₁ e₂′

    lam₋  : ∀ {e e′} →
            ¬ WHNF e → e CBN.⇒ e′ →
            lam e ⇒ lam e′

    lam₊  : ∀ {e e′} →
            WHNF e → e ⇒ e′ →
            lam e ⇒ lam e′


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction (Garcia-Perez, et al.)

module NO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {e₁ e₂} →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁₋  : ∀ {e₁ e₂ e₁′} →
             ¬ WHNF e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₁₊  : ∀ {e₁ e₂ e₁′} →
             NAXNF e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction, alternative (Pierce)
-- ∙ With corrected app₁ rule

module NO′ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {e₁ e₂} →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-value reduction (no reference)
-- ∙ With weak normal forms

module CBV where
  data _⇒_ {n} : Rel₀ (Tm n) where
    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             WNF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

    applam : ∀ {e₁ e₂} →
             WNF e₂ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-value reduction (Pierce)
-- ∙ With values

module CBV₀ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             V e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

    applam : ∀ {e₁ e₂} →
             V e₂ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]


---------------------------------------------------------------------------------------------------------------
--
-- Small-step applicative order reduction (no reference)

module AO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    app₂   : ∀ {e₁ e₂ e₂′} →
             e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

    app₁   : ∀ {e₁ e₂ e₁′} →
             NF e₂ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    applam : ∀ {e₁ e₂} →
             NF e₁ → NF e₂ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Small-step hybrid applicative order reduction (no reference)


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head spine reduction (no reference)

module HS where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e e′} →
             e ⇒ e′ →
             lam e ⇒ lam e′

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    applam : ∀ {e₁ e₂} →
             HNF e₁ →
             app (lam e₁) e₂ ⇒ e₁ [ e₂ ]


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Small-step head reduction (no reference)


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Small-step hybrid normal order reduction (no reference)


---------------------------------------------------------------------------------------------------------------
