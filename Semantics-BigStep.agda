---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep where

open import Syntax-Predicates public


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-name reduction (Sestoft)
-- From terms to weak head normal forms

module CBN where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e} →
             lam e ⇓ lam e

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ ⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ ⇓ e₁′ → NA e₁′ →
             app e₁ e₂ ⇓ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-name reduction (no reference)
-- From terms to values

module CBN₀ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e} →
             lam e ⇓ lam e

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ ⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction, post-CBN fragment (Garcia-Perez, et al.)
-- From weak head normal forms to normal forms

module NO₊ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var : ∀ {x} →
          var x ⇓ var x

    lam : ∀ {e e′ e″} →
          e CBN.⇓ e′ → e′ ⇓ e″ →
          lam e ⇓ lam e″

    app : ∀ {e₁ e₂ e₁′ e₂′ e₂″} →
          NA e₁ → e₁ ⇓ e₁′ → e₂ CBN.⇓ e₂′ → e₂′ ⇓ e₂″ →
          app e₁ e₂ ⇓ app e₁′ e₂″


---------------------------------------------------------------------------------------------------------------
--
-- Big-step normal order reduction (Sestoft)
-- From terms to normal forms

module NO where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ CBN.⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ CBN.⇓ e₁′ → NA e₁′ → e₁′ ⇓ e₁″ → e₂ ⇓ e₂′ →
             app e₁ e₂ ⇓ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-value reduction (Sestoft)
-- From terms to weak normal forms

module CBV where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e} →
             lam e ⇓ lam e

    applam : ∀ {e₁ e₂ e₁′ e₂′ e′} →
             e₁ ⇓ lam e₁′ → e₂ ⇓ e₂′ → e₁′ [ e₂′ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′ e₂′} →
             e₁ ⇓ e₁′ → NA e₁′ → e₂ ⇓ e₂′ →
             app e₁ e₂ ⇓ app e₁′ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-value reduction (Pierce)
-- From terms to values

module CBV₀ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    lam    : ∀ {e} →
             lam e ⇓ lam e

    applam : ∀ {e₁ e₂ e₁′ e₂′ e′} →
             e₁ ⇓ lam e₁′ → e₂ ⇓ e₂′ → V e₂′ → e₁′ [ e₂′ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step applicative order reduction (Sestoft)
-- From terms to normal forms

module AO where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e₂′ e′} →
             e₁ ⇓ lam e₁′ → e₂ ⇓ e₂′ → e₁′ [ e₂′ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′ e₂′} →
             e₁ ⇓ e₁′ → NA e₁′ → e₂ ⇓ e₂′ →
             app e₁ e₂ ⇓ app e₁′ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid applicative order reduction (Sestoft)
-- From terms to normal forms

module HAO where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e₂′ e′} →
             e₁ CBV.⇓ lam e₁′ → e₂ ⇓ e₂′ → e₁′ [ e₂′ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ CBV.⇓ e₁′ → NA e₁′ → e₁′ ⇓ e₁″ → e₂ ⇓ e₂′ →
             app e₁ e₂ ⇓ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head spine reduction (Sestoft)
-- From terms to head normal forms

module HS where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ ⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ ⇓ e₁′ → NA e₁′ →
             app e₁ e₂ ⇓ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head reduction (Sestoft)
-- From terms to head normal forms

module H where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ CBN.⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ CBN.⇓ e₁′ → NA e₁′ →
             app e₁ e₂ ⇓ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid normal order reduction (Sestoft)
-- From terms to normal forms

module HNO where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var    : ∀ {x} →
             var x ⇓ var x

    lam    : ∀ {e e′} →
             e ⇓ e′ →
             lam e ⇓ lam e′

    applam : ∀ {e₁ e₂ e₁′ e′} →
             e₁ HS.⇓ lam e₁′ → e₁′ [ e₂ ] ⇓ e′ →
             app e₁ e₂ ⇓ e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ HS.⇓ e₁′ → NA e₁′ → e₁′ ⇓ e₁″ → e₂ ⇓ e₂′ →
             app e₁ e₂ ⇓ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
