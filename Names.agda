module Names where

open import Prelude
open import Vec


--------------------------------------------------------------------------------


Name : Set
Name = String

Names : Nat → Set
Names n = Vec Name n


--------------------------------------------------------------------------------
