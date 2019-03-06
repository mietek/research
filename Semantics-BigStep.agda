---------------------------------------------------------------------------------------------------------------

module Semantics-BigStep where

open import Syntax-Predicates public


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-name reduction (Sestoft’s bn)
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
-- Big-step normal order reduction (Sestoft’s no)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ✘ “Reduces arguments before substitution” is incorrect; arguments are reduced eventually
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
-- Small-step normal order reduction, two-stage, second stage (Garcia-Perez, et al.)
-- ✔ From weak head normal forms to normal forms

module NO₂ where
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
-- Big-step call-by-value reduction (Sestoft’s bv)
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
-- Big-step applicative order reduction (Sestoft’s ao)
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
-- Big-step hybrid applicative order reduction (Sestoft’s ha)
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
-- Big-step head spine reduction (Sestoft’s he)
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
-- Big-step head reduction (Sestoft’s modified he)
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

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ CBN.⇓ e₁′ → NA e₁′ →
             app e₁ e₂ ⇓ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid normal order reduction (Sestoft’s hn)
-- ✔ From terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ✘ “Reduces arguments before substitution” is incorrect; arguments are reduced eventually
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
