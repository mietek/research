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
      [_]_ : Ty⋆ → Ty → Ty

    Ty⋆ : Set
    Ty⋆ = List Ty

  record BoxTy : Set where
    constructor [_]_
    field
      Δ : Ty⋆
      A : Ty

  BoxTy⋆ : Set
  BoxTy⋆ = List BoxTy


-- Types and vectors of types.

module IMCMLVec where
  open import PreludeVec public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •    : Ty
      _⇒_ : Ty → Ty → Ty
      [_]_ : ∀ {d} → Ty⋆ d → Ty → Ty

    Ty⋆ : Nat → Set
    Ty⋆ g = Vec Ty g

  record BoxTy : Set where
    constructor [_]_
    field
      {d} : Nat
      Δ   : Ty⋆ d
      A   : Ty

  BoxTy⋆ : Nat → Set
  BoxTy⋆ d = Vec BoxTy d
