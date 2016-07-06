module IPC.Core where

open import Common.Context public
open import Common.Sequence public


-- Propositions of intuitionistic propositional calculus (IPC).

infixl 5 _∧_
infixr 3 _⇒_
data Ty : Set where
  α_   : Atom → Ty
  _⇒_ : Ty → Ty → Ty
  ⊤   : Ty
  _∧_  : Ty → Ty → Ty

infix 3 _⇔_
_⇔_ : Ty → Ty → Ty
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)
