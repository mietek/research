module IPC where

open import Prelude public


-- Types.

infixr 7 _⇒_
data Ty : Set where
  •    : Ty
  _⇒_ : Ty → Ty → Ty


-- Lists of types.

module IPCList where
  open import PreludeList public

  Ty⋆ : Set
  Ty⋆ = List Ty


-- Vectors of types.

module IPCVec where
  open import PreludeVec public

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g
