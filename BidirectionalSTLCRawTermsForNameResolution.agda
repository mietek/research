module BidirectionalSTLCRawTermsForNameResolution where

open import Prelude
open import Vec
open import STLCTypes


--------------------------------------------------------------------------------


Name : Set
Name = String

Names : Nat → Set
Names n = Vec Name n


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
