{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------

module A201903.2-2-Semantics-SmallStep where

open import A201903.1-2-Syntax-Predicates public
open Binary public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-name reduction (Pierce)

module CBN where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction (Pierce)
-- ∙ Corrected app₁ rule not to go to non-abstractions

module NO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam    : ∀ {s e e′} →
             e ⇒ e′ →
             lam s e ⇒ lam s e′

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step normal order reduction, second phase (Garcia-Perez, et al.)
-- ✓ Goes from weak head normal forms

module NO₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    cbn-lam  : ∀ {s e e′} →
               ¬ WHNF e → e CBN.⇒ e′ →
               lam s e ⇒ lam s e′

    lam      : ∀ {s e e′} →
               WHNF e → e ⇒ e′ →
               lam s e ⇒ lam s e′

    app₁     : ∀ {e₁ e₂ e₁′} →
               NAXNF e₁ → e₁ ⇒ e₁′ →
               app e₁ e₂ ⇒ app e₁′ e₂

    cbn-app₂ : ∀ {e₁ e₂ e₂′} →
               NANF e₁ → ¬ WHNF e₂ → e₂ CBN.⇒ e₂′ →
               app e₁ e₂ ⇒ app e₁ e₂′

    app₂     : ∀ {e₁ e₂ e₂′} →
               NANF e₁ → WHNF e₂ → e₂ ⇒ e₂′ →
               app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step call-by-value reduction (Pierce)
-- ∙ Modified applam and app₂ rules to go from weak normal forms instead of values

module CBV where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             WNF e₂ →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             WNF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step applicative order reduction (no reference)

module AO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             NF e₁ → NF e₂ →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam    : ∀ {s e e′} →
             e ⇒ e′ →
             lam s e ⇒ lam s e′

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid applicative order reduction (no reference)

module HAO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam   : ∀ {s e₁ e₂} →
               NF e₂ →
               app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam      : ∀ {s e e′} →
               e ⇒ e′ →
               lam s e ⇒ lam s e′

    cbv-app₁ : ∀ {e₁ e₂ e₁′} →
               e₁ CBV.⇒ e₁′ →
               app e₁ e₂ ⇒ app e₁′ e₂

    app₁     : ∀ {e₁ e₂ e₁′} →
               NAWNF e₁ → e₁ ⇒ e₁′ →
               app e₁ e₂ ⇒ app e₁′ e₂

    app₂ₐ    : ∀ {s e₁ e₂ e₂′} →
               e₂ ⇒ e₂′ →
               app (lam s e₁) e₂ ⇒ app (lam s e₁) e₂′

    app₂     : ∀ {e₁ e₂ e₂′} →
               NANF e₁ → e₂ ⇒ e₂′ →
               app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head spine reduction (no reference)

module HS where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             HNF e₁ →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam    : ∀ {s e e′} →
             e ⇒ e′ →
             lam s e ⇒ lam s e′

    app₁   : ∀ {e₁ e₂ e₁′} →
             e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head reduction (no reference)

module H where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam    : ∀ {s e e′} →
             e ⇒ e′ →
             lam s e ⇒ lam s e′

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step head reduction, second phase (no reference)
-- ✓ Goes from weak head normal forms

module H₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    cbn-lam : ∀ {s e e′} →
              ¬ WHNF e → e CBN.⇒ e′ →
              lam s e ⇒ lam s e′

    lam     : ∀ {s e e′} →
              WHNF e → e ⇒ e′ →
              lam s e ⇒ lam s e′

    app₁    : ∀ {e₁ e₂ e₁′} →
              NAXNF e₁ → e₁ ⇒ e₁′ →
              app e₁ e₂ ⇒ app e₁′ e₂

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid normal order reduction (no reference)

module HNO where
  data _⇒_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂} →
             HNF e₁ →
             app (lam s e₁) e₂ ⇒ e₁ [ e₂ ]

    lam    : ∀ {s e e′} →
             e ⇒ e′ →
             lam s e ⇒ lam s e′

    app₁ₐ  : ∀ {s e₁ e₁′ e₂} →
             ¬ HNF e₁ → e₁ ⇒ e₁′ →
             app (lam s e₁) e₂ ⇒ app (lam s e₁′) e₂

    app₁   : ∀ {e₁ e₂ e₁′} →
             NA e₁ → e₁ ⇒ e₁′ →
             app e₁ e₂ ⇒ app e₁′ e₂

    app₂   : ∀ {e₁ e₂ e₂′} →
             NANF e₁ → e₂ ⇒ e₂′ →
             app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
--
-- Small-step hybrid normal order reduction, second phase (no reference)
-- ✓ Goes from head normal forms

module HNO₂ where
  data _⇒_ {n} : Rel₀ (Tm n) where
    lam     : ∀ {s e e′} →
              HNF e → e ⇒ e′ →
              lam s e ⇒ lam s e′

    app₁    : ∀ {e₁ e₂ e₁′} →
              NAXNF e₁ → e₁ ⇒ e₁′ →
              app e₁ e₂ ⇒ app e₁′ e₂

    hs-app₂ : ∀ {e₁ e₂ e₂′} →
              NANF e₁ → ¬ HNF e₂ → e₂ HS.⇒ e₂′ →
              app e₁ e₂ ⇒ app e₁ e₂′

    app₂    : ∀ {e₁ e₂ e₂′} →
              NANF e₁ → HNF e₂ → e₂ ⇒ e₂′ →
              app e₁ e₂ ⇒ app e₁ e₂′

  open DerivedEquipment _⇒_ public


---------------------------------------------------------------------------------------------------------------
