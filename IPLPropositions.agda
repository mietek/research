module IPLPropositions where

open import Prelude


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


--------------------------------------------------------------------------------
