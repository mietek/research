module NewBasicILP.UntypedSyntax.Common where

open import Common.UntypedContext public


-- Types parametrised by a closed, untyped representation of syntax.

module ClosedSyntax
    (Rep : Set)
  where

  infixr 9 [_]_
  infixl 8 _∧_
  infixr 6 _▻_
  data Ty : Set where
    α_   : Atom → Ty
    _▻_  : Ty → Ty → Ty
    [_]_ : Rep → Ty → Ty
    _∧_  : Ty → Ty → Ty
    ⊤   : Ty


  -- Additional useful types.

  infixr 6 _▻⋯▻_
  _▻⋯▻_ : Cx Ty → Ty → Ty
  ⌀       ▻⋯▻ B = B
  (Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)
