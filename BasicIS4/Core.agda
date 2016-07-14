module BasicIS4.Core where

open import Common.Context public


-- Propositions of intuitionistic modal logic S4, without disjunction, falsehood, and possibility.

infixl 7 _∧_
infixr 5 _▷_
data Ty : Set where
  ᴬ_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  □_  : Ty → Ty
  ⫪  : Ty
  _∧_ : Ty → Ty → Ty

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)
