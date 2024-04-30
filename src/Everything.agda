module A201706.Everything where

import A201706.Prelude
import A201706.PreludeList
import A201706.PreludeVec

import A201706.IPC
import A201706.IPCSyntaxNoTerms
import A201706.IPCSemantics
import A201706.IPCSemanticsExperimental
import A201706.IPCNormalisationNoTerms
import A201706.IPCNormalisationExperimentalNoTerms

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
import A201706.IS4
import A201706.IS4SyntaxNoTerms
import A201706.IS4SemanticsNoTerms
import A201706.IS4NormalisationNoTerms

-- Intuitionistic contextual modal logic
-- [Γ]A
import A201706.ICML
import A201706.ICMLSyntaxNoTerms
import A201706.ICMLSemanticsNoTerms
import A201706.ICMLNormalisationNoTerms

-- Intuitionistic modally-contextual modal logic
-- [Δ]A
import A201706.IMCML
import A201706.IMCMLSyntaxNoTerms
import A201706.IMCMLSemanticsNoTerms -- TODO
import A201706.IMCMLNormalisationNoTerms -- TODO

-- Intuitionistic syntax-recursive modal logic
-- [Δ;Γ]A
import A201706.ISML
import A201706.ISMLSyntaxNoTerms

-- Intuitionistic logic of proofs
-- [M]A
import A201706.ILP
import A201706.ILPSyntaxTerms

-- Intuitionistic contextual logic of proofs
-- [Γ⊦M]A
import A201706.ICLP
import A201706.ICLPSyntaxTerms

-- Intuitionistic modally-contextual logic of proofs
-- [Δ⊦M]A
import A201706.IMCLP
import A201706.IMCLPSyntaxTerms

-- Intuitionistic syntax-recursive logic of proofs
-- [Δ;Γ⊦M]A
import A201706.ISLP
import A201706.ISLPSyntaxTerms
