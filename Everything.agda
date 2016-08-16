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

-- Linear Hilbert-style axiomatic formalisation of syntax.
import BasicIPC.Syntax.HilbertLinear

-- Hilbert-style axiomatic formalisation of syntax.
import BasicIPC.Syntax.Hilbert

-- Gentzen-style natural deduction formalisation of syntax.
import BasicIPC.Syntax.Gentzen
import BasicIPC.Syntax.GentzenNormalForm
import BasicIPC.Syntax.GentzenSpinalNormalForm

-- Translation between different formalisations of syntax.
import BasicIPC.Syntax.Translation


-- Basic Tarski-style denotational semantics.
import BasicIPC.Semantics.Tarski

-- Tarski-style semantics with a closed syntactic component, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiClosedCoquandDybjer

-- Tarski-style semantics with a Hilbert-style closed syntax representation.
import BasicIPC.Semantics.TarskiClosedHilbert

-- Tarski-style semantics with a syntactic component, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiCoquandDybjer

-- Tarski-style semantics with a Hilbert-style syntax representation.
import BasicIPC.Semantics.TarskiHilbert

-- Tarski-style semantics with a Gentzen-style syntax representation.
import BasicIPC.Semantics.TarskiGentzen

-- Kripke-style possible worlds semantics, based on the Gödel translation.
import BasicIPC.Semantics.KripkeGodel

-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.
import BasicIPC.Semantics.KripkeMcKinseyTarski


import BasicIPC.Metatheory.ClosedHilbert-Tarski
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedHilbert

import BasicIPC.Metatheory.Hilbert-Tarski
import BasicIPC.Metatheory.Hilbert-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.Hilbert-TarskiClosedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiCoquandDybjer
import BasicIPC.Metatheory.Hilbert-TarskiHilbert
import BasicIPC.Metatheory.Hilbert-KripkeGodel
import BasicIPC.Metatheory.Hilbert-KripkeMcKinseyTarski

import BasicIPC.Metatheory.Gentzen-Tarski
import BasicIPC.Metatheory.Gentzen-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.Gentzen-TarskiCoquandDybjer
import BasicIPC.Metatheory.Gentzen-TarskiGentzen
import BasicIPC.Metatheory.Gentzen-KripkeGodel
import BasicIPC.Metatheory.Gentzen-KripkeMcKinseyTarski

import BasicIPC.Metatheory.GentzenNormalForm-KripkeGodel
import BasicIPC.Metatheory.GentzenNormalForm-KripkeMcKinseyTarski

import BasicIPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution




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

-- Linear Hilbert-style axiomatic formalisation of syntax.
import BasicIS4.Syntax.HilbertLinear

-- Hilbert-style axiomatic formalisation of syntax.
import BasicIS4.Syntax.Hilbert

-- Gentzen-style natural deduction formalisation of syntax, after Bierman-de Paiva.
import BasicIS4.Syntax.Gentzen

-- Linear Hilbert-style axiomatic formalisation of syntax with separate modal context.
import BasicIS4.Syntax.DyadicHilbertLinear

-- Hilbert-style axiomatic formalisation of syntax with separate modal context.
import BasicIS4.Syntax.DyadicHilbert

-- Gentzen-style axiomatic formalisation of syntax with separate modal context, after Pfenning-Davies.
import BasicIS4.Syntax.DyadicGentzen

-- Gentzen-style axiomatic formalisation of syntax with separate relational context, after Basin-Matthews-Viganò.
import BasicIS4.Syntax.LabelledGentzen

-- Translation between different formalisations of syntax.
import BasicIS4.Syntax.Translation

-- Translated equipment for Hilbert-style closed syntax.
import BasicIS4.Syntax.ClosedHilbertTranslatedEquipment


-- Tarski-style semantics with a syntactic component, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiGabbayNanevski
import BasicIS4.Semantics.TarskiGabbayNanevskiMk1

-- Tarski-style semantics with a syntactic component, after Coquand-Dybjer.
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

import BasicIS4.Metatheory.Hilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.Hilbert-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.Hilbert-TarskiCoquandDybjer
import BasicIS4.Metatheory.Hilbert-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.Hilbert-KripkeOno
import BasicIS4.Metatheory.Hilbert-KripkeBozicDosen
import BasicIS4.Metatheory.Hilbert-KripkeEwald
import BasicIS4.Metatheory.Hilbert-KripkeAlechinaEtAl

import BasicIS4.Metatheory.Gentzen-TarskiGabbayNanevski
import BasicIS4.Metatheory.Gentzen-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.Gentzen-TarskiCoquandDybjer
import BasicIS4.Metatheory.Gentzen-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.Gentzen-KripkeOno
import BasicIS4.Metatheory.Gentzen-KripkeBozicDosen
import BasicIS4.Metatheory.Gentzen-KripkeEwald
import BasicIS4.Metatheory.Gentzen-KripkeAlechinaEtAl

import BasicIS4.Metatheory.DyadicHilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.DyadicHilbert-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.DyadicHilbert-TarskiCoquandDybjer
import BasicIS4.Metatheory.DyadicHilbert-TarskiCoquandDybjerMk1
import BasicIS4.Metatheory.DyadicHilbert-KripkeOno
import BasicIS4.Metatheory.DyadicHilbert-KripkeBozicDosen
import BasicIS4.Metatheory.DyadicHilbert-KripkeEwald
import BasicIS4.Metatheory.DyadicHilbert-KripkeAlechinaEtAl

import BasicIS4.Metatheory.DyadicGentzen-TarskiGabbayNanevski
import BasicIS4.Metatheory.DyadicGentzen-TarskiGabbayNanevskiMk1
import BasicIS4.Metatheory.DyadicGentzen-TarskiCoquandDybjer
import BasicIS4.Metatheory.DyadicGentzen-KripkeOno
import BasicIS4.Metatheory.DyadicGentzen-KripkeBozicDosen
import BasicIS4.Metatheory.DyadicGentzen-KripkeEwald
import BasicIS4.Metatheory.DyadicGentzen-KripkeAlechinaEtAl




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
