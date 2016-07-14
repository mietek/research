module BasicIPC.Core where

open import Common.Context public


-- Connectives of intuitionistic propositional calculus (IPC), without disjunction and falsehood.

infixl 7 _∧_
infixr 5 _▷_
data Ty : Set where
  ᴬ_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  ⫪  : Ty
  _∧_ : Ty → Ty → Ty

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)
