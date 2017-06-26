module IMCML where

open import Prelude public


-- Types and lists of types.

module IMCMLList where
  open import PreludeList public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •    : Ty
      _⇒_ : Ty → Ty → Ty
      [_]_ : BoxTy⋆ → Ty → Ty

    record BoxTy : Set where
      inductive
      constructor [_]_
      field
        BoxTy→BoxTy⋆ : BoxTy⋆
        BoxTy→Ty     : Ty

    BoxTy⋆ : Set
    BoxTy⋆ = List BoxTy
  open BoxTy public

  Ty⋆ : Set
  Ty⋆ = List Ty


-- Types and vectors of types.

module IMCMLVec where
  open import PreludeVec public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •    : Ty
      _⇒_ : Ty → Ty → Ty
      [_]_ : ∀ {d} → BoxTy⋆ d → Ty → Ty

    record BoxTy : Set where
      inductive
      constructor [_]_
      field
        {d}           : Nat
        BoxTy→BoxTy⋆ : BoxTy⋆ d
        BoxTy→Ty     : Ty

    BoxTy⋆ : Nat → Set
    BoxTy⋆ d = Vec BoxTy d
  open BoxTy public

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g
