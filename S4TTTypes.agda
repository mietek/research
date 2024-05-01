module S4TTTypes where

open import Prelude
open import Vec


--------------------------------------------------------------------------------


open import S4Propositions public
  renaming (Form to Type ; _≟ₚ_ to _≟ₜ_)


Types : Nat → Set
Types g = Vec Type g


Asserts : Nat → Set
Asserts d = Vec Assert d


--------------------------------------------------------------------------------
