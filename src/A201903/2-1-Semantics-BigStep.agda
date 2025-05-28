{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------

module A201903.2-1-Semantics-BigStep where

open import A201903.1-2-Syntax-Predicates public
open Binary public


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-name reduction (Sestoft’s BN)
-- ✓ Goes from terms to weak head normal forms
-- ∙ Does not reduce under λ-abstractions
-- ∙ Does not reduce arguments before substitution
-- ∙ “Reduces the leftmost outermost redex not inside a λ-abstraction first”
-- ∙ “Treats free variables as non-strict data constructors”

module CBN where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e′} →
             e₁ ⟱ lam s e₁′ → e₁′ [ e₂ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e} →
             lam s e ⟱ lam s e

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ ⟱ e₁′ → NA e₁′ →
             app e₁ e₂ ⟱ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step normal order reduction (Sestoft’s NO)
-- ✓ Goes from terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ “Reduces arguments before substitution” is unclear; before substitution, arguments are reduced to WHNF,
--   and to NF only after substitution
-- ∙ “Reduces the leftmost outermost redex first”
-- ∙ Normalising

module NO where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e′} →
             e₁ CBN.⟱ lam s e₁′ → e₁′ [ e₂ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ CBN.⟱ e₁′ → NA e₁′ → e₁′ ⟱ e₁″ → e₂ ⟱ e₂′ →
             app e₁ e₂ ⟱ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step normal order reduction, second phase (Garcia-Perez, et al.)
-- ✓ Goes from weak head normal forms to normal forms

module NO₂ where
  data _⟱_ {n} : Rel₀ (Tm n) where
    var : ∀ {s x} →
          var s x ⟱ var s x

    lam : ∀ {s e e′ e″} →
          e CBN.⟱ e′ → e′ ⟱ e″ →
          lam s e ⟱ lam s e″

    app : ∀ {e₁ e₂ e₁′ e₂′ e₂″} →
          NAXNF e₁ → e₁ ⟱ e₁′ → e₂ CBN.⟱ e₂′ → e₂′ ⟱ e₂″ →
          app e₁ e₂ ⟱ app e₁′ e₂″


---------------------------------------------------------------------------------------------------------------
--
-- Big-step call-by-value reduction (Sestoft’s BV)
-- ✓ Goes from terms to weak normal forms
-- ∙ Does not reduce under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces the leftmost innermost redex not inside a λ-abstraction first”
-- ∙ “Treats free variables as strict data constructors”

module CBV where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e₂′ e′} →
             e₁ ⟱ lam s e₁′ → e₂ ⟱ e₂′ → e₁′ [ e₂′ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e} →
             lam s e ⟱ lam s e

    app    : ∀ {e₁ e₂ e₁′ e₂′} →
             e₁ ⟱ e₁′ → NA e₁′ → e₂ ⟱ e₂′ →
             app e₁ e₂ ⟱ app e₁′ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step applicative order reduction (Sestoft’s AO)
-- ✓ Goes from terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces the leftmost innermost redex first”
-- ∙ Not normalising

module AO where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e₂′ e′} →
             e₁ ⟱ lam s e₁′ → e₂ ⟱ e₂′ → e₁′ [ e₂′ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′ e₂′} →
             e₁ ⟱ e₁′ → NA e₁′ → e₂ ⟱ e₂′ →
             app e₁ e₂ ⟱ app e₁′ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid applicative order reduction (Sestoft’s HA)
-- ✓ Goes from terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Reduces arguments before substitution
-- ∙ “Reduces inside λ-abstractions only in argument positions”
-- ∙ “Relates to CBV in the same way that NO relates to CBN” is unclear; the shape of the NO and HAO rules
--   is the same, but the operation of the NO and HAO rules is not the same
-- ∙ “Resembles Paulson’s CBV, which works in two phases” is unclear; HAO does not work in two phases

module HAO where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e₂′ e′} →
             e₁ CBV.⟱ lam s e₁′ → e₂ ⟱ e₂′ → e₁′ [ e₂′ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ CBV.⟱ e₁′ → NA e₁′ → e₁′ ⟱ e₁″ → e₂ ⟱ e₂′ →
             app e₁ e₂ ⟱ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head spine reduction (Sestoft’s HE)
-- ✓ Goes from terms to head normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ Does not reduce arguments before substitution
-- ∙ “Reduces inside λ-abstractions, but only in head position”

module HS where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e′} →
             e₁ ⟱ lam s e₁′ → e₁′ [ e₂ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′} →
             e₁ ⟱ e₁′ → NA e₁′ →
             app e₁ e₂ ⟱ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head reduction (Sestoft’s modified HE)
-- ✓ Goes from terms to head normal forms
-- ∙ “Only head redexes are contracted”

module H where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e′} →
             e₁ CBN.⟱ lam s e₁′ → e₁′ [ e₂ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′ e₁″} →
             e₁ CBN.⟱ e₁′ → NA e₁′ → e₁′ ⟱ e₁″ →
             app e₁ e₂ ⟱ app e₁″ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step head reduction, second phase (no reference)
-- ✓ Goes from weak head normal forms to head normal forms

module H₂ where
  data _⟱_ {n} : Rel₀ (Tm n) where
    var : ∀ {s x} →
          var s x ⟱ var s x

    lam : ∀ {s e e′ e″} →
          e CBN.⟱ e′ → e′ ⟱ e″ →
          lam s e ⟱ lam s e″

    app : ∀ {e₁ e₂ e₁′} →
          NAXNF e₁ → e₁ ⟱ e₁′ →
          app e₁ e₂ ⟱ app e₁′ e₂


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid normal order reduction (Sestoft’s HN)
-- ✓ Goes from terms to normal forms
-- ∙ Reduces under λ-abstractions
-- ∙ “Reduces arguments before substitution” is unclear; before substitution, arguments are reduced to HNF,
--   and to NF only after substitution
-- ∙ Normalising

module HNO where
  data _⟱_ {n} : Rel₀ (Tm n) where
    applam : ∀ {s e₁ e₂ e₁′ e′} →
             e₁ HS.⟱ lam s e₁′ → e₁′ [ e₂ ] ⟱ e′ →
             app e₁ e₂ ⟱ e′

    var    : ∀ {s x} →
             var s x ⟱ var s x

    lam    : ∀ {s e e′} →
             e ⟱ e′ →
             lam s e ⟱ lam s e′

    app    : ∀ {e₁ e₂ e₁′ e₁″ e₂′} →
             e₁ HS.⟱ e₁′ → NA e₁′ → e₁′ ⟱ e₁″ → e₂ ⟱ e₂′ →
             app e₁ e₂ ⟱ app e₁″ e₂′


---------------------------------------------------------------------------------------------------------------
--
-- Big-step hybrid normal order reduction, second phase (no reference)
-- ✓ Goes from head normal forms to normal forms

module HNO₂ where
  data _⟱_ {n} : Rel₀ (Tm n) where
    var : ∀ {s x} →
          var s x ⟱ var s x

    lam : ∀ {s e e′} →
          HNF e → e ⟱ e′ →
          lam s e ⟱ lam s e′

    app : ∀ {e₁ e₂ e₁′ e₂′ e₂″} →
          NAXNF e₁ → e₁ ⟱ e₁′ → e₂ HS.⟱ e₂′ → e₂′ ⟱ e₂″ →
          app e₁ e₂ ⟱ app e₁′ e₂″


---------------------------------------------------------------------------------------------------------------
