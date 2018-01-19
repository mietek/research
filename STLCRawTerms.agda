module STLCRawTermsForNameResolution where

open import Prelude
open import Names
open import STLCTypes


--------------------------------------------------------------------------------


data RawTerm : Set
  where
    VAR   : Name → RawTerm
    LAM   : Name → RawTerm → RawTerm
    APP   : RawTerm → RawTerm → RawTerm
    CHECK : RawTerm → Type → RawTerm


--------------------------------------------------------------------------------
