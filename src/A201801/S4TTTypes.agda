{-# OPTIONS --rewriting #-}

module A201801.S4TTTypes where

open import A201801.Prelude
open import A201801.Vec


--------------------------------------------------------------------------------


open import A201801.S4Propositions public
  renaming (Form to Type ; _≟ₚ_ to _≟ₜ_)


Types : Nat → Set
Types g = Vec Type g


Asserts : Nat → Set
Asserts d = Vec Assert d


--------------------------------------------------------------------------------
