module Common.Semantics where

open import Common public


-- Special products for glueing.

infix 5 _⅋_
record Glue (Syn : Set) (Sem : Set) : Set where
  constructor _⅋_
  field
    syn : Syn
    sem : Sem

open Glue public
