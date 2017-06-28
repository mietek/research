module ICML where

open import Prelude public


-- Types and lists of types.

module ICMLList where
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
      Γ : Ty⋆
      A : Ty

  BoxTy⋆ : Set
  BoxTy⋆ = List BoxTy


-- Types and vectors of types.

module ICMLVec where
  open import PreludeVec public

  mutual
    infixr 7 _⇒_
    data Ty : Set where
      •    : Ty
      _⇒_ : Ty → Ty → Ty
      [_]_ : ∀ {g} → Ty⋆ g → Ty → Ty

    Ty⋆ : Nat → Set
    Ty⋆ g = Vec Ty g

  record BoxTy : Set where
    constructor [_]_
    field
      {g} : Nat
      Γ   : Ty⋆ g
      A   : Ty

  BoxTy⋆ : Nat → Set
  BoxTy⋆ d = Vec BoxTy d
