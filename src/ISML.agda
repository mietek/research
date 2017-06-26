module ISML where

open import Prelude public


-- Types and lists of types.

module ISMLList where
  open import PreludeList public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •      : Ty
      _⇒_   : Ty → Ty → Ty
      [_⁏_]_ : BoxTy⋆ → Ty⋆ → Ty → Ty

    record BoxTy : Set where
      inductive
      constructor [_⁏_]_
      field
        BoxTy→BoxTy⋆ : BoxTy⋆
        BoxTy→Ty⋆    : Ty⋆
        BoxTy→Ty     : Ty

    Ty⋆ : Set
    Ty⋆ = List Ty

    BoxTy⋆ : Set
    BoxTy⋆ = List BoxTy
  open BoxTy public


-- Types and vectors of types.

module ISMLVec where
  open import PreludeVec public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •      : Ty
      _⇒_   : Ty → Ty → Ty
      [_⁏_]_ : ∀ {d g} → BoxTy⋆ d → Ty⋆ g → Ty → Ty

    record BoxTy : Set where
      inductive
      constructor [_⁏_]_
      field
        {d}           : Nat
        {g}           : Nat
        BoxTy→BoxTy⋆ : BoxTy⋆ d
        BoxTy→Ty⋆    : Ty⋆ g
        BoxTy→Ty     : Ty

    Ty⋆ : Nat → Set
    Ty⋆ g = Vec Ty g

    BoxTy⋆ : Nat → Set
    BoxTy⋆ d = Vec BoxTy d
  open BoxTy public
