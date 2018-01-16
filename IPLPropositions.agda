module IPLPropositions where

open import Prelude
open import Vec


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop


--------------------------------------------------------------------------------


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


Truths : Nat → Set
Truths g = Vec Truth g


--------------------------------------------------------------------------------
