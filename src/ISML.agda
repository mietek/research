module ISML where

open import Prelude public


-- Lists of types.

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


-- Vectors of types.

module ISMLVec where
  open import PreludeVec public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •      : Ty
      _⇒_   : Ty → Ty → Ty
      [_⁏_]_ : ∀ {q p} → BoxTy⋆ q → Ty⋆ p → Ty → Ty

    record BoxTy : Set where
      inductive
      constructor [_⁏_]_
      field
        {q}           : Nat
        {p}           : Nat
        BoxTy→BoxTy⋆ : BoxTy⋆ q
        BoxTy→Ty⋆    : Ty⋆ p
        BoxTy→Ty     : Ty

    Ty⋆ : Nat → Set
    Ty⋆ g = Vec Ty g

    BoxTy⋆ : Nat → Set
    BoxTy⋆ d = Vec BoxTy d
  open BoxTy public
