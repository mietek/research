{-

https://github.com/mietek/hilbert-gentzen

An Agda formalisation of intuitionistic propositional calculus, modal logic S4,
and logic of proofs.  Work in progress.

Made by Miëtek Bak.  Published under the MIT X11 license.

-}

module Everything where

import Common
import Common.Context
import Common.ContextPair
import Common.Predicate
import Common.PredicateBasedContext




-- Basic intuitionistic propositional calculus, without ∨ or ⊥.


-- Common syntax.
import New.BasicIPC.Syntax.Common

-- List-shaped Hilbert-style axiomatic formalisation of closed syntax.
import New.BasicIPC.Syntax.Closed.HilbertList

-- Tree-shaped Hilbert-style axiomatic formalisation of closed syntax.
import New.BasicIPC.Syntax.Closed.HilbertTree

-- List-shaped Hilbert-style axiomatic formalisation of open syntax.
import New.BasicIPC.Syntax.Open.HilbertList

-- Tree-shaped Hilbert-style axiomatic formalisation of open syntax.
import New.BasicIPC.Syntax.Open.HilbertTree

-- Tree-shaped Gentzen-style natural deduction formalisation of open syntax.
import New.BasicIPC.Syntax.Open.GentzenTree
import New.BasicIPC.Syntax.Open.GentzenTreeNormalForm
import New.BasicIPC.Syntax.Open.GentzenTreeSpinalNormalForm

-- Translation between different formalisations of syntax.
import New.BasicIPC.Syntax.Translation


-- Basic Tarski-style denotational semantics.
import New.BasicIPC.Semantics.Tarski.Basic

-- Tarski-style denotational semantics with a syntactic component, after Coquand-Dybjer.
import New.BasicIPC.Semantics.Tarski.CoquandDybjer
import New.BasicIPC.Semantics.Tarski.CoquandDybjerHilbert

-- Kripke-style possible worlds semantics, based on the Gödel translation.
import New.BasicIPC.Semantics.Kripke.Godel

-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.
import New.BasicIPC.Semantics.Kripke.McKinseyTarski


import New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.Basic
import New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.CoquandDybjer
import New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.CoquandDybjerHilbert

import New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.Basic
import New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.CoquandDybjer
import New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.CoquandDybjerHilbert
import New.BasicIPC.Metatheory.Open.HilbertTree.Kripke.Godel
import New.BasicIPC.Metatheory.Open.HilbertTree.Kripke.McKinseyTarski

import New.BasicIPC.Metatheory.Open.GentzenTree.Tarski.Basic
import New.BasicIPC.Metatheory.Open.GentzenTree.Tarski.CoquandDybjer
import New.BasicIPC.Metatheory.Open.GentzenTree.Kripke.Godel
import New.BasicIPC.Metatheory.Open.GentzenTree.Kripke.GodelNormalForm
import New.BasicIPC.Metatheory.Open.GentzenTree.Kripke.McKinseyTarski
import New.BasicIPC.Metatheory.Open.GentzenTree.Kripke.McKinseyTarskiNormalForm

import New.BasicIPC.Metatheory.OpenSyntax.Gentzen.HereditarySubstitution




-- Intuitionistic propositional calculus.

import IPC
import IPC.TarskiSemantics
import IPC.KripkeSemantics
import IPC.Hilbert.List
import IPC.Hilbert.ListWithContext
import IPC.Hilbert.Tree
import IPC.Hilbert.Tree.TarskiSoundness
import IPC.Hilbert.Tree.TarskiBasicCompleteness
import IPC.Hilbert.TreeWithContext
import IPC.Hilbert.TreeWithContext.TarskiSoundness
import IPC.Hilbert.TreeWithContext.TarskiBasicCompleteness
import IPC.Hilbert.TreeWithContext.KripkeSoundness -- FIXME
import IPC.Hilbert.Translation
import IPC.Gentzen
import IPC.Gentzen.TarskiSoundness -- FIXME
import IPC.Gentzen.TarskiBasicCompleteness -- FIXME
import IPC.Gentzen.KripkeSoundness
import IPC.Gentzen.KripkeBasicCompleteness
import IPC.Gentzen.KripkeCompleteness
import IPC.Gentzen.HereditarySubstitution
import IPC.Translation




-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.

import New.BasicIS4.Syntax.Common
import New.BasicIS4.Syntax.ClosedHilbertLinear
import New.BasicIS4.Syntax.ClosedHilbert
import New.BasicIS4.Syntax.OpenHilbertLinear
import New.BasicIS4.Syntax.OpenHilbert
import New.BasicIS4.Syntax.OpenGentzen
import New.BasicIS4.Syntax.OpenDyadicHilbertLinear
import New.BasicIS4.Syntax.OpenDyadicHilbert
import New.BasicIS4.Syntax.OpenDyadicGentzen
import New.BasicIS4.Syntax.OpenLabelledGentzen
import New.BasicIS4.Syntax.Translation
import New.BasicIS4.Syntax.TranslatedClosedHilbertEquipment

import New.BasicIS4.Semantics.TarskiGabbayNanevski
import New.BasicIS4.Semantics.TarskiCoquandDybjer
import New.BasicIS4.Semantics.TarskiGabbayNanevskiMk1
import New.BasicIS4.Semantics.TarskiCoquandDybjerMk1
import New.BasicIS4.Semantics.KripkeOno
import New.BasicIS4.Semantics.KripkeBozicDosen
import New.BasicIS4.Semantics.KripkeEwaldEtAl
import New.BasicIS4.Semantics.KripkeAlechinaEtAl
import New.BasicIS4.Semantics.KripkeCanonicalModelEquipment
import New.BasicIS4.Semantics.KripkeNonCanonicalModelEquipment
import New.BasicIS4.Semantics.KripkeDyadicCanonicalModelEquipment
import New.BasicIS4.Semantics.KripkeDyadicNonCanonicalModelEquipment

import New.BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevski
import New.BasicIS4.Metatheory.ClosedHilbert-TarskiCoquandDybjer
import New.BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevskiMk1
import New.BasicIS4.Metatheory.ClosedHilbert-TarskiCoquandDybjerMk1

import New.BasicIS4.Metatheory.OpenHilbert-TarskiGabbayNanevski
import New.BasicIS4.Metatheory.OpenHilbert-TarskiCoquandDybjer
import New.BasicIS4.Metatheory.OpenHilbert-TarskiGabbayNanevskiMk1
import New.BasicIS4.Metatheory.OpenHilbert-TarskiCoquandDybjerMk1
import New.BasicIS4.Metatheory.OpenHilbert-KripkeOno
import New.BasicIS4.Metatheory.OpenHilbert-KripkeBozicDosen
import New.BasicIS4.Metatheory.OpenHilbert-KripkeEwaldEtAl
import New.BasicIS4.Metatheory.OpenHilbert-KripkeAlechinaEtAl

import New.BasicIS4.Metatheory.OpenGentzen-TarskiGabbayNanevski
import New.BasicIS4.Metatheory.OpenGentzen-TarskiCoquandDybjer
import New.BasicIS4.Metatheory.OpenGentzen-TarskiGabbayNanevskiMk1
import New.BasicIS4.Metatheory.OpenGentzen-TarskiCoquandDybjerMk1
import New.BasicIS4.Metatheory.OpenGentzen-KripkeOno
import New.BasicIS4.Metatheory.OpenGentzen-KripkeBozicDosen
import New.BasicIS4.Metatheory.OpenGentzen-KripkeEwaldEtAl
import New.BasicIS4.Metatheory.OpenGentzen-KripkeAlechinaEtAl

import New.BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevski
import New.BasicIS4.Metatheory.OpenDyadicHilbert-TarskiCoquandDybjer
import New.BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevskiMk1
import New.BasicIS4.Metatheory.OpenDyadicHilbert-TarskiCoquandDybjerMk1
import New.BasicIS4.Metatheory.OpenDyadicHilbert-KripkeOno
import New.BasicIS4.Metatheory.OpenDyadicHilbert-KripkeBozicDosen
import New.BasicIS4.Metatheory.OpenDyadicHilbert-KripkeEwaldEtAl
import New.BasicIS4.Metatheory.OpenDyadicHilbert-KripkeAlechinaEtAl

import New.BasicIS4.Metatheory.OpenDyadicGentzen-TarskiGabbayNanevski
import New.BasicIS4.Metatheory.OpenDyadicGentzen-TarskiCoquandDybjer
import New.BasicIS4.Metatheory.OpenDyadicGentzen-TarskiGabbayNanevskiMk1
import New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeOno
import New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeBozicDosen
import New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeEwaldEtAl
import New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeAlechinaEtAl


-- Intuitionistic logic of proofs, without ∨, ⊥, or +.

import BasicILP.Indirect
import BasicILP.Indirect.Hilbert.Sequential
import BasicILP.Indirect.Hilbert.Nested
import BasicILP.Indirect.Gentzen
-- import BasicILP.Indirect.Translation
import BasicILP.Direct.Hilbert.Sequential
import BasicILP.Direct.Hilbert.Nested
import BasicILP.Direct.Gentzen
-- import BasicILP.Direct.Translation
import BasicILP.Translation
