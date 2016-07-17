module BasicIS4.Core where

open import Common.Context public


-- Propositions of intuitionistic modal logic S4, without disjunction, falsehood, or possibility.

infixl 7 _∧_
infixr 5 _▷_
data Ty : Set where
  α_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  □_  : Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)


-- Additional useful propositions.

□⋆_ : Cx Ty → Cx Ty
□⋆ ⌀       = ⌀
□⋆ (Γ , A) = □⋆ Γ , □ A
