module BasicIPC.Core where

open import Common.Context public


-- Propositions of intuitionistic propositional calculus (IPC), without disjunction or falsehood.

infixl 7 _∧_
infixr 5 _▷_
data Ty : Set where
  α_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)