module A201706.ISML where

open import A201706.Prelude public


-- Types and lists of types.

module ISMLList where
  open import A201706.PreludeList public

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
        Δ : BoxTy⋆
        Γ : Ty⋆
        A : Ty

    Ty⋆ : Set
    Ty⋆ = List Ty

    BoxTy⋆ : Set
    BoxTy⋆ = List BoxTy


-- Types and vectors of types.

module ISMLVec where
  open import A201706.PreludeVec public

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
        {d} : Nat
        {g} : Nat
        Δ   : BoxTy⋆ d
        Γ   : Ty⋆ g
        A   : Ty

    Ty⋆ : Nat → Set
    Ty⋆ g = Vec Ty g

    BoxTy⋆ : Nat → Set
    BoxTy⋆ d = Vec BoxTy d
