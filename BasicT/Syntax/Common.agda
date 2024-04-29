-- TODO
-- Common syntax.

module A201607.BasicT.Syntax.Common where

open import A201607.Common.Context public


-- Types, or propositions.

infixl 9 _∧_
infixr 7 _▻_
data Ty : Set where
  α_   : Atom → Ty
  _▻_  : Ty → Ty → Ty
  _∧_  : Ty → Ty → Ty
  ⊤   : Ty
  BOOL : Ty
  NAT  : Ty


-- Additional useful types.

infix 7 _▻◅_
_▻◅_ : Ty → Ty → Ty
A ▻◅ B = (A ▻ B) ∧ (B ▻ A)

infixr 7 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
∅       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)

infixr 7 _▻⋯▻⋆_
_▻⋯▻⋆_ : Cx Ty → Cx Ty → Ty
Γ ▻⋯▻⋆ ∅       = ⊤
Γ ▻⋯▻⋆ (Ξ , A) = (Γ ▻⋯▻⋆ Ξ) ∧ (Γ ▻⋯▻ A)
