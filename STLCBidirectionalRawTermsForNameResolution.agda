module STLCBidirectionalRawTermsForNameResolution where

open import Prelude
open import Names
open import STLCTypes


--------------------------------------------------------------------------------


mutual
  data RawTermₗ : Set
    where
      LAM : Name → RawTermₗ → RawTermₗ
      INF : RawTermᵣ → RawTermₗ

  data RawTermᵣ : Set
    where
      VAR : Name → RawTermᵣ
      APP : RawTermᵣ → RawTermₗ → RawTermᵣ
      CHK : RawTermₗ → Type → RawTermᵣ


--------------------------------------------------------------------------------
