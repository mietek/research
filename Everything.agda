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
import New.BasicIPC.Syntax.ClosedHilbertLinear

-- Tree-shaped Hilbert-style axiomatic formalisation of closed syntax.
import New.BasicIPC.Syntax.ClosedHilbert

-- List-shaped Hilbert-style axiomatic formalisation of open syntax.
import New.BasicIPC.Syntax.OpenHilbertLinear

-- Tree-shaped Hilbert-style axiomatic formalisation of open syntax.
import New.BasicIPC.Syntax.OpenHilbert

-- Tree-shaped Gentzen-style natural deduction formalisation of open syntax.
import New.BasicIPC.Syntax.OpenGentzen
import New.BasicIPC.Syntax.OpenGentzenNormalForm
import New.BasicIPC.Syntax.OpenGentzenSpinalNormalForm

-- Translation between different formalisations of syntax.
import New.BasicIPC.Syntax.Translation


-- Basic Tarski-style denotational semantics.
import New.BasicIPC.Semantics.Tarski

-- Tarski-style denotational semantics with a syntactic component, after Coquand-Dybjer.
import New.BasicIPC.Semantics.TarskiCoquandDybjer
import New.BasicIPC.Semantics.TarskiCoquandDybjerMk1

-- Kripke-style possible worlds semantics, based on the Gödel translation.
import New.BasicIPC.Semantics.KripkeGodel

-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.
import New.BasicIPC.Semantics.KripkeMcKinseyTarski


import New.BasicIPC.Metatheory.ClosedHilbert-Tarski
import New.BasicIPC.Metatheory.ClosedHilbert-TarskiCoquandDybjer
import New.BasicIPC.Metatheory.ClosedHilbert-TarskiCoquandDybjerMk1

import New.BasicIPC.Metatheory.OpenHilbert-Tarski
import New.BasicIPC.Metatheory.OpenHilbert-TarskiCoquandDybjer
import New.BasicIPC.Metatheory.OpenHilbert-TarskiCoquandDybjerMk1
import New.BasicIPC.Metatheory.OpenHilbert-KripkeGodel
import New.BasicIPC.Metatheory.OpenHilbert-KripkeMcKinseyTarski

import New.BasicIPC.Metatheory.OpenGentzen-Tarski
import New.BasicIPC.Metatheory.OpenGentzen-TarskiCoquandDybjer
import New.BasicIPC.Metatheory.OpenGentzen-KripkeGodel
import New.BasicIPC.Metatheory.OpenGentzen-KripkeMcKinseyTarski
import New.BasicIPC.Metatheory.OpenGentzenNormalForm-KripkeGodel
import New.BasicIPC.Metatheory.OpenGentzenNormalForm-KripkeMcKinseyTarski

import New.BasicIPC.Metatheory.OpenGentzen-HereditarySubstitution




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
