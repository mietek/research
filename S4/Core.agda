module S4.Core where

open import Common.Context public
open import Common.Sequence public


-- Types of intuitionistic modal logic S4, with necessity, but without possibility.

infixl 5 _∧_
infixr 3 _⇒_
data Ty : Set where
  α_   : Atom → Ty
  _⇒_ : Ty → Ty → Ty
  □_   : Ty → Ty
  ⊤   : Ty
  _∧_  : Ty → Ty → Ty

infix 3 _⇔_
_⇔_ : Ty → Ty → Ty
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)
