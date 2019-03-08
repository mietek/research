---------------------------------------------------------------------------------------------------------------

module 1-4-Semantics-BigStep where

open import 1-2-Syntax-Predicates public


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-name reduction (Sestoft’s BN)
-- ✔ From terms to weak head normal forms
-- ∙ Does not reduce under λ-abstractions
-- ∙ Does not reduce arguments before substitution
-- ∙ “Reduces the leftmost outermost redex not inside a λ-abstraction first”
-- ∙ “Treats free variables as non-strict data constructors”

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
-- Big-step normal order reduction (Sestoft’s NO)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ✘ “Reduces arguments before substitution” is imprecise;
--   arguments are reduced to WHNF before substitution, and to NF after substitution
-- ∙ “Reduces the leftmost outermost redex first”
-- ∙ Normalising

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
-- Big-step normal order reduction, second stage (Garcia-Perez, et al.)
-- ✔ From weak head normal forms to normal forms

module NO₂ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var : ∀ {x} →
          var x ⇓ var x

    lam : ∀ {e e′ e″} →
          e CBN.⇓ e′ → e′ ⇓ e″ →
          lam e ⇓ lam e″

    app : ∀ {e₁ e₂ e₁′ e₂′ e₂″} →
          NAXNF e₁ → e₁ ⇓ e₁′ → e₂ CBN.⇓ e₂′ → e₂′ ⇓ e₂″ →
          app e₁ e₂ ⇓ app e₁′ e₂″


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-value reduction (Sestoft’s BV)
-- ✔ From terms to weak normal forms
-- ∙ Does not reduce under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces the leftmost innermost redex not inside a λ-abstraction first”
-- ∙ “Treats free variables as strict data constructors”

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
-- Big-step applicative order reduction (Sestoft’s AO)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces the leftmost innermost redex first”
-- ∙ Not normalising

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
-- Big-step hybrid applicative order reduction (Sestoft’s HA)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces inside λ-abstractions only in argument positions”
-- ∙ “Relates to CBV in the same way that NO relates to CBN”

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
-- Big-step head spine reduction (Sestoft’s HE)
-- ✔ From terms to head normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Does not reduce arguments before substitution
-- ∙ “Reduces inside λ-abstractions, but only in head position”

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
-- Big-step head reduction (Sestoft’s modified HE)
-- ✔ From terms to head normal forms
-- ∙ “Only head redexes are contracted”

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

    app    : ∀ {e₁ e₂ e₁′ e₁″} →
             e₁ CBN.⇓ e₁′ → NA e₁′ → e₁′ ⇓ e₁″ →
             app e₁ e₂ ⇓ app e₁″ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head reduction, second stage (no reference)
-- ✔ From weak head normal forms to head normal forms

module H₂ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var : ∀ {x} →
          var x ⇓ var x

    lam : ∀ {e e′ e″} →
          e CBN.⇓ e′ → e′ ⇓ e″ →
          lam e ⇓ lam e″

    app : ∀ {e₁ e₂ e₁′} →
          NAXNF e₁ → e₁ ⇓ e₁′ →
          app e₁ e₂ ⇓ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid normal order reduction (Sestoft’s HN)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ✘ “Reduces arguments before substitution” is imprecise;
--   arguments are reduced to HNF before substitution, and to NF after substitution
-- ∙ Normalising

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
--
-- Big-step hybrid normal order reduction, second stage (no reference)
-- ✔ From head normal forms to normal forms

module HNO₂ where
  data _⇓_ {n} : Rel₀ (Tm n) where
    var : ∀ {x} →
          var x ⇓ var x

    lam : ∀ {e e′} →
          HNF e → e ⇓ e′ →
          lam e ⇓ lam e′

-- TODO
--    lam : ∀ {e e′ e″} →
--          e HS.⇓ e′ → e′ ⇓ e″ →
--          lam e ⇓ lam e″

    app : ∀ {e₁ e₂ e₁′ e₂′ e₂″} →
          NAXNF e₁ → e₁ ⇓ e₁′ → e₂ HS.⇓ e₂′ → e₂′ ⇓ e₂″ →
          app e₁ e₂ ⇓ app e₁′ e₂″


---------------------------------------------------------------------------------------------------------------
