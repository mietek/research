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
import BasicIPC.Syntax.Common

-- Linear Hilbert-style axiomatic formalisation of closed syntax.
import BasicIPC.Syntax.ClosedHilbertLinear

-- Hilbert-style axiomatic formalisation of closed syntax.
import BasicIPC.Syntax.ClosedHilbert

-- Linear Hilbert-style axiomatic formalisation of open syntax.
import BasicIPC.Syntax.OpenHilbertLinear

-- Hilbert-style axiomatic formalisation of open syntax.
import BasicIPC.Syntax.OpenHilbert

-- Gentzen-style natural deduction formalisation of open syntax.
import BasicIPC.Syntax.OpenGentzen
import BasicIPC.Syntax.OpenGentzenNormalForm
import BasicIPC.Syntax.OpenGentzenSpinalNormalForm

-- Translation between different formalisations of syntax.
import BasicIPC.Syntax.Translation


-- Basic Tarski-style denotational semantics.
import BasicIPC.Semantics.Tarski

-- Tarski-style denotational semantics with a syntactic component, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiCoquandDybjer
import BasicIPC.Semantics.TarskiCoquandDybjerMk1

-- Kripke-style possible worlds semantics, based on the Gödel translation.
import BasicIPC.Semantics.KripkeGodel

-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.
import BasicIPC.Semantics.KripkeMcKinseyTarski


import BasicIPC.Metatheory.ClosedHilbert-Tarski
import BasicIPC.Metatheory.ClosedHilbert-TarskiCoquandDybjer
import BasicIPC.Metatheory.ClosedHilbert-TarskiCoquandDybjerMk1

import BasicIPC.Metatheory.OpenHilbert-Tarski
import BasicIPC.Metatheory.OpenHilbert-TarskiCoquandDybjer
import BasicIPC.Metatheory.OpenHilbert-TarskiCoquandDybjerMk1
import BasicIPC.Metatheory.OpenHilbert-KripkeGodel
import BasicIPC.Metatheory.OpenHilbert-KripkeMcKinseyTarski

import BasicIPC.Metatheory.OpenGentzen-Tarski
import BasicIPC.Metatheory.OpenGentzen-TarskiCoquandDybjer
import BasicIPC.Metatheory.OpenGentzen-KripkeGodel
import BasicIPC.Metatheory.OpenGentzen-KripkeMcKinseyTarski
import BasicIPC.Metatheory.OpenGentzenNormalForm-KripkeGodel
import BasicIPC.Metatheory.OpenGentzenNormalForm-KripkeMcKinseyTarski

import BasicIPC.Metatheory.OpenGentzenSpinalNormalForm-HereditarySubstitution




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


-- Common syntax.
import BasicIS4.Syntax.Common

-- Linear Hilbert-style axiomatic formalisation of closed syntax.
import BasicIS4.Syntax.ClosedHilbertLinear

-- Hilbert-style axiomatic formalisation of closed syntax.
import BasicIS4.Syntax.ClosedHilbert

-- Linear Hilbert-style axiomatic formalisation of open syntax.
import BasicIS4.Syntax.OpenHilbertLinear

-- Hilbert-style axiomatic formalisation of open syntax.
import BasicIS4.Syntax.OpenHilbert

-- Gentzen-style natural deduction formalisation of open syntax, after Bierman-de Paiva.
import BasicIS4.Syntax.OpenGentzen

-- Linear Hilbert-style axiomatic formalisation of open syntax with separate modal context.
import BasicIS4.Syntax.OpenDyadicHilbertLinear

-- Hilbert-style axiomatic formalisation of open syntax with separate modal context.
import BasicIS4.Syntax.OpenDyadicHilbert

-- Gentzen-style axiomatic formalisation of open syntax with separate modal context, after Pfenning-Davies.
import BasicIS4.Syntax.OpenDyadicGentzen

-- Gentzen-style axiomatic formalisation of open syntax with separate relational context, after Basin-Matthews-Viganò.
import BasicIS4.Syntax.OpenLabelledGentzen

-- Translation between different formalisations of syntax.
import BasicIS4.Syntax.Translation

-- Translated equipment for Hilbert-style closed syntax.
import BasicIS4.Syntax.TranslatedClosedHilbertEquipment


-- Tarski-style denotational semantics with a syntactic component, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiGabbayNanevski
import BasicIS4.Semantics.TarskiGabbayNanevskiMk1

-- Tarski-style denotational semantics with a syntactic component, after Coquand-Dybjer.
import BasicIS4.Semantics.TarskiCoquandDybjer
import BasicIS4.Semantics.TarskiCoquandDybjerMk1

-- Kripke-style possible worlds semantics, after Ono.
import BasicIS4.Semantics.KripkeOno

-- Kripke-style possible worlds semantics, after Božić-Došen.
import BasicIS4.Semantics.KripkeBozicDosen

-- Kripke-style possible worlds semantics, after Ewald, Servi, and Plotkin-Stirling.
import BasicIS4.Semantics.KripkeEwald

-- Kripke-style possible worlds semantics, after Alechina-Mendler-de Paiva-Ritter.
import BasicIS4.Semantics.KripkeAlechinaEtAl

-- Canonical and non-canonical model equipment for Kripke-style semantics.
import BasicIS4.Semantics.KripkeCanonicalModelEquipment
import BasicIS4.Semantics.KripkeNonCanonicalModelEquipment
import BasicIS4.Semantics.KripkeDyadicCanonicalModelEquipment
import BasicIS4.Semantics.KripkeDyadicNonCanonicalModelEquipment


import BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.ClosedHilbert-TarskiCoquandDybjer
import BasicIS4.Metatheory.ClosedHilbert-TarskiCoquandDybjerMk1

import BasicIS4.Metatheory.OpenHilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.OpenHilbert-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.OpenHilbert-TarskiCoquandDybjer
import BasicIS4.Metatheory.OpenHilbert-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.OpenHilbert-KripkeOno
import BasicIS4.Metatheory.OpenHilbert-KripkeBozicDosen
import BasicIS4.Metatheory.OpenHilbert-KripkeEwald
import BasicIS4.Metatheory.OpenHilbert-KripkeAlechinaEtAl

import BasicIS4.Metatheory.OpenGentzen-TarskiGabbayNanevski
import BasicIS4.Metatheory.OpenGentzen-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.OpenGentzen-TarskiCoquandDybjer
import BasicIS4.Metatheory.OpenGentzen-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.OpenGentzen-KripkeOno
import BasicIS4.Metatheory.OpenGentzen-KripkeBozicDosen
import BasicIS4.Metatheory.OpenGentzen-KripkeEwald
import BasicIS4.Metatheory.OpenGentzen-KripkeAlechinaEtAl

import BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.OpenDyadicHilbert-TarskiCoquandDybjer
import BasicIS4.Metatheory.OpenDyadicHilbert-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.OpenDyadicHilbert-KripkeOno
import BasicIS4.Metatheory.OpenDyadicHilbert-KripkeBozicDosen
import BasicIS4.Metatheory.OpenDyadicHilbert-KripkeEwald
import BasicIS4.Metatheory.OpenDyadicHilbert-KripkeAlechinaEtAl

import BasicIS4.Metatheory.OpenDyadicGentzen-TarskiGabbayNanevski
import BasicIS4.Metatheory.OpenDyadicGentzen-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.OpenDyadicGentzen-TarskiCoquandDybjer
import BasicIS4.Metatheory.OpenDyadicGentzen-KripkeOno
import BasicIS4.Metatheory.OpenDyadicGentzen-KripkeBozicDosen
import BasicIS4.Metatheory.OpenDyadicGentzen-KripkeEwald
import BasicIS4.Metatheory.OpenDyadicGentzen-KripkeAlechinaEtAl


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
