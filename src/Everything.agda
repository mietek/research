module Everything where

import Prelude
import PreludeList
import PreludeVec

import IPC
import IPCSyntaxNoTerms
import IPCSemantics
import IPCNormalisationNoTerms

--     IMCLP──────ISLP                     [Δ⊦M]A──[Δ;Γ⊦M]A
--      ╱│        ╱│    IS4         □A      ╱│        ╱│
--     ╱ │       ╱ │    ICML      [Γ]A     ╱ │       ╱ │
--  IMCML┼─────ISML│    IMCML     [Δ]A   [Δ]A┼────[Δ;Γ]A
--    │  │      │  │    ISML    [Δ;Γ]A    │  │      │  │
--    │  │      │  │    ILP       [M]A    │  │      │  │
--    │ ILP─────┼─ICLP  ICLP    [Γ⊦M]A    │ [M]A────┼[Γ⊦M]A
--    │ ╱       │ ╱     IMCLP   [Δ⊦M]A    │ ╱       │ ╱
--    │╱        │╱      ISLP  [Δ;Γ⊦M]A    │╱        │╱
--   IS4───────ICML                       □A───────[Γ]A

-- □A
import IS4
import IS4SyntaxNoTerms

-- [Γ]A
import ICML
import ICMLSyntaxNoTerms

-- [Δ]A
import IMCML
import IMCMLSyntaxNoTerms

-- [Δ;Γ]A
import ISML
import ISMLSyntaxNoTerms

-- [M]A
import ILP
import ILPSyntaxTerms

-- [Γ⊦M]A
import ICLP
import ICLPSyntaxTerms

-- [Δ⊦M]A
import IMCLP
import IMCLPSyntaxTerms

-- [Δ;Γ⊦M]A
import ISLP
import ISLPSyntaxTerms
