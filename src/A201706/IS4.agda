{-# OPTIONS --rewriting #-}

module A201706.IS4 where

open import A201706.Prelude public


-- Types.

infixr 7 _⇒_
data Ty : Set where
  •    : Ty
  _⇒_ : Ty → Ty → Ty
  □_   : Ty → Ty

record BoxTy : Set where
  constructor □_
  field
    A : Ty


-- Lists of types.

module IS4List where
  open import A201706.PreludeList public

  Ty⋆ : Set
  Ty⋆ = List Ty

  BoxTy⋆ : Set
  BoxTy⋆ = List BoxTy


-- Vectors of types.

module IS4Vec where
  open import A201706.PreludeVec public

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g

  BoxTy⋆ : Nat → Set
  BoxTy⋆ d = Vec BoxTy d
