module STLCTypes where

open import Prelude
open import Vec


--------------------------------------------------------------------------------


open import IPLPropositions public
  renaming (Form to Type ; _≟ₚ_ to _≟ₜ_)


Types : Nat → Set
Types g = Vec Type g


--------------------------------------------------------------------------------
