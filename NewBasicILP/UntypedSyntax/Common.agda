module NewBasicILP.UntypedSyntax.Common where

open import Common.UntypedContext public


-- Types parametrised by closed, untyped representations.

module ClosedSyntax
    (Proof : Set)
  where

  infixr 10 _⦂_
  infixl 9 _∧_
  infixr 7 _▻_
  data Ty : Set where
    α_  : Atom → Ty
    _▻_ : Ty → Ty → Ty
    _⦂_ : Proof → Ty → Ty
    _∧_ : Ty → Ty → Ty
    ⊤  : Ty


  -- Additional useful types.

  infixr 7 _▻⋯▻_
  _▻⋯▻_ : Cx Ty → Ty → Ty
  ∅       ▻⋯▻ B = B
  (Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)
