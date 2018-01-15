module S4Propositions where

open import Prelude


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop
    □_   : Prop → Prop


--------------------------------------------------------------------------------


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop


--------------------------------------------------------------------------------
