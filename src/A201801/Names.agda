module A201801.Names where

open import A201801.Prelude
open import A201801.Vec


--------------------------------------------------------------------------------


Name : Set
Name = String

Names : Nat → Set
Names n = Vec Name n


--------------------------------------------------------------------------------
