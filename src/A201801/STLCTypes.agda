{-# OPTIONS --rewriting #-}

module A201801.STLCTypes where

open import A201801.Prelude
open import A201801.Vec


--------------------------------------------------------------------------------


open import A201801.IPLPropositions public
  renaming (Form to Type ; _≟ₚ_ to _≟ₜ_)


Types : Nat → Set
Types g = Vec Type g


--------------------------------------------------------------------------------
