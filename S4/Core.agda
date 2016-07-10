module S4.Core where

open import Common.Context public


-- Propositions of intuitionistic modal logic S4, restricted to necessity.

infixl 5 _∧_
infixr 3 _⊃_
data Ty : Set where
  α_  : Atom → Ty
  _⊃_ : Ty → Ty → Ty
  □_  : Ty → Ty
  ι   : Ty
  _∧_ : Ty → Ty → Ty

infix 3 _⊃⊂_
_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = (A ⊃ B) ∧ (B ⊃ A)
