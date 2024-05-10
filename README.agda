module README where


--------------------------------------------------------------------------------

-- original version, plus unfinished attempt at adding products and coproducts

open import AbelChapman
open import AbelChapmanPlus
open import Experiments


--------------------------------------------------------------------------------

-- common

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.StrongBisimilarity
open import AbelChapmanExtended.Convergence


--------------------------------------------------------------------------------

-- added products and coproducts

open import AbelChapmanExtended2.Syntax
open import AbelChapmanExtended2.OPE
open import AbelChapmanExtended2.Renaming
open import AbelChapmanExtended2.Normalization
open import AbelChapmanExtended2.Semantics
open import AbelChapmanExtended2.RenamingLemmas.OPE
open import AbelChapmanExtended2.RenamingLemmas.Normalization1
open import AbelChapmanExtended2.RenamingLemmas.Normalization2
open import AbelChapmanExtended2.RenamingLemmas.Convergence
open import AbelChapmanExtended2.RenamingLemmas.Semantics
open import AbelChapmanExtended2.Reflection
open import AbelChapmanExtended2.Termination
open import AbelChapmanExtended2.Examples


--------------------------------------------------------------------------------

-- experiments

open import TowardsAltArtemov.SyntaxCatholic
open import TowardsAltArtemov.SyntaxSimple
open import TowardsAltArtemov.SyntaxSimpleCatholic
open import TowardsAltArtemov.SyntaxSimpleCatholicRadical
open import TowardsAltArtemov.NormalizationCatholic
open import TowardsAltArtemov.NormalizationSimple
open import TowardsAltArtemov.NormalizationSimpleCatholic


--------------------------------------------------------------------------------

-- TODO: separate

open import AltArtemov.README


--------------------------------------------------------------------------------
