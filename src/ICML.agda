module A201706.ICML where

open import A201706.Prelude public


-- Types and lists of types.

module ICMLList where
  open import A201706.PreludeList public

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
  open import A201706.PreludeVec public

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
