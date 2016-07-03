module IPC.Core where

open import Common.Core public


-- Propositions of intuitionistic propositional calculus (IPC).

infixl 5 _∧_
infixl 4 _∨_
infixr 3 _⇒_
data Ty : Set where
  ι    : Atom → Ty
  _⇒_ : Ty → Ty → Ty
  _∧_  : Ty → Ty → Ty
  _∨_  : Ty → Ty → Ty
  ⊥   : Ty

¬_ : Ty → Ty
¬ A = A ⇒ ⊥

infix 3 _⇔_
_⇔_ : Ty → Ty → Ty
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)


open import Common.Context (Ty) public
open import Common.Sequence (Ty) public
