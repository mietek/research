module STLCBidirectionalTermsForNameResolution where

open import Prelude
open import Names
open import STLCTypes


--------------------------------------------------------------------------------


mutual
  data PreTermₗ : Set
    where
      LAM : Name → PreTermₗ → PreTermₗ
      INF : PreTermᵣ → PreTermₗ

  data PreTermᵣ : Set
    where
      VAR : Name → PreTermᵣ
      APP : PreTermᵣ → PreTermₗ → PreTermᵣ
      CHK : PreTermₗ → Type → PreTermᵣ


--------------------------------------------------------------------------------
