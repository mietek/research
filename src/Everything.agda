module Everything where

import Prelude
import PreludeList
import PreludeVec

import IPC
import IPCSyntaxNoTerms
import IPCSemantics
import IPCNormalisationNoTerms

--     [Δ⊦M]A──[Δ;Γ⊦M]A
--      ╱│        ╱│
--     ╱ │       ╱ │
--   [Δ]A┼────[Δ;Γ]A
--    │  │      │  │
--    │  │      │  │
--    │ [M]A────┼[Γ⊦M]A
--    │ ╱       │ ╱
--    │╱        │╱
--    □A───────[Γ]A
--
--  IS4    □A
--  ICML   [Γ]A
--  IMCML  [Δ]A
--  ISML   [Δ;Γ]A
--  ILP    [M]A
--  ICLP   [Γ⊦M]A
--  IMCLP  [Δ⊦M]A
--  ISLP   [Δ;Γ⊦M]A
--
--     IMCLP──────ISLP
--      ╱│        ╱│
--     ╱ │       ╱ │
--  IMCML┼─────ISML│
--    │  │      │  │
--    │  │      │  │
--    │ ILP─────┼─ICLP
--    │ ╱       │ ╱
--    │╱        │╱
--   IS4───────ICML

import IS4
import IS4SyntaxNoTerms

import ICML
import ICMLSyntaxNoTerms

import IMCML
import IMCMLSyntaxNoTerms

import ISML
import ISMLSyntaxNoTerms

-- TODO: ILP, ICLP, IMCLP, ISLP
