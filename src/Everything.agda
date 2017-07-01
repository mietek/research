module Everything where

import Prelude
import PreludeList
import PreludeVec

import IPC
import IPCSyntaxNoTerms
import IPCSemantics
import IPCSemanticsExperimental
import IPCNormalisationNoTerms
import IPCNormalisationExperimentalNoTerms

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

-- Intuitionistic modal logic S4
-- □A
import IS4
import IS4SyntaxNoTerms
import IS4SemanticsNoTerms
import IS4NormalisationNoTerms

-- Intuitionistic contextual modal logic
-- [Γ]A
import ICML
import ICMLSyntaxNoTerms
import ICMLSemanticsNoTerms
import ICMLNormalisationNoTerms -- TODO

-- Intuitionistic modally-contextual modal logic
-- [Δ]A
import IMCML
import IMCMLSyntaxNoTerms

-- Intuitionistic syntax-recursive modal logic
-- [Δ;Γ]A
import ISML
import ISMLSyntaxNoTerms

-- Intuitionistic logic of proofs
-- [M]A
import ILP
import ILPSyntaxTerms

-- Intuitionistic contextual logic of proofs
-- [Γ⊦M]A
import ICLP
import ICLPSyntaxTerms

-- Intuitionistic modally-contextual logic of proofs
-- [Δ⊦M]A
import IMCLP
import IMCLPSyntaxTerms

-- Intuitionistic syntax-recursive logic of proofs
-- [Δ;Γ⊦M]A
import ISLP
import ISLPSyntaxTerms
