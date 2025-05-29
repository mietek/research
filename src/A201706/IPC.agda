{-# OPTIONS --rewriting #-}

module A201706.IPC where

open import A201706.Prelude public


-- Types.

infixr 7 _⇒_
data Ty : Set where
  •    : Ty
  _⇒_ : Ty → Ty → Ty


-- Lists of types.

module IPCList where
  open import A201706.PreludeList public

  Ty⋆ : Set
  Ty⋆ = List Ty


-- Vectors of types.

module IPCVec where
  open import A201706.PreludeVec public

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g
