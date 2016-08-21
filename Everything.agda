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

-- Hilbert-style axiomatic formalisation of closed syntax, as linear sequences.
import BasicIPC.Syntax.ClosedHilbertLinear

-- Hilbert-style axiomatic formalisation of closed syntax.
import BasicIPC.Syntax.ClosedHilbert

-- Hilbert-style axiomatic formalisation of syntax, as linear sequences.
import BasicIPC.Syntax.HilbertLinear

-- Hilbert-style axiomatic formalisation of syntax.
import BasicIPC.Syntax.Hilbert

-- Gentzen-style natural deduction formalisation of syntax.
import BasicIPC.Syntax.Gentzen
import BasicIPC.Syntax.GentzenNormalForm
import BasicIPC.Syntax.GentzenSpinalNormalForm

-- Translation between different formalisations of syntax.
import BasicIPC.Syntax.Translation


-- Basic Tarski-style denotational semantics, for soundness only.
import BasicIPC.Semantics.BasicTarski

-- Tarski-style semantics with implicit closed syntax representation, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiClosedCoquandDybjer

-- Tarski-style semantics with explicit Hilbert-style closed syntax representation.
import BasicIPC.Semantics.TarskiClosedHilbert

-- Tarski-style semantics with implicit syntax representation, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiCoquandDybjer

-- Tarski-style semantics with explicit Hilbert-style syntax representation.
import BasicIPC.Semantics.TarskiHilbert

-- Tarski-style semantics with explicit Gentzen-style syntax representation.
import BasicIPC.Semantics.TarskiGentzen

-- Tarski-style semantics with explicit contexts.
import BasicIPC.Semantics.Tarski

-- Kripke-style semantics, based on the McKinsey-Tarski translation.
import BasicIPC.Semantics.KripkeMcKinseyTarski

-- Kripke-style semantics, based on the Gödel translation.
import BasicIPC.Semantics.KripkeGodel


import BasicIPC.Metatheory.ClosedHilbert-BasicTarski
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedHilbert

import BasicIPC.Metatheory.Hilbert-BasicTarski
import BasicIPC.Metatheory.Hilbert-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.Hilbert-TarskiClosedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiCoquandDybjer
import BasicIPC.Metatheory.Hilbert-TarskiHilbert
import BasicIPC.Metatheory.Hilbert-TarskiGentzen
import BasicIPC.Metatheory.Hilbert-Tarski
import BasicIPC.Metatheory.Hilbert-KripkeMcKinseyTarski
import BasicIPC.Metatheory.Hilbert-KripkeGodel

import BasicIPC.Metatheory.Gentzen-BasicTarski
import BasicIPC.Metatheory.Gentzen-TarskiClosedCoquandDybjer
import BasicIPC.Metatheory.Gentzen-TarskiCoquandDybjer
import BasicIPC.Metatheory.Gentzen-TarskiGentzen
import BasicIPC.Metatheory.Gentzen-Tarski
import BasicIPC.Metatheory.Gentzen-KripkeMcKinseyTarski
import BasicIPC.Metatheory.Gentzen-KripkeGodel

import BasicIPC.Metatheory.GentzenNormalForm-Tarski
import BasicIPC.Metatheory.GentzenNormalForm-KripkeMcKinseyTarski
import BasicIPC.Metatheory.GentzenNormalForm-KripkeGodel

import BasicIPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution




-- Intuitionistic propositional calculus. (To be rewritten.)

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

-- Hilbert-style axiomatic formalisation of closed syntax, as linear sequences.
import BasicIS4.Syntax.ClosedHilbertLinear

-- Hilbert-style axiomatic formalisation of closed syntax.
import BasicIS4.Syntax.ClosedHilbert

-- Hilbert-style axiomatic formalisation of syntax, as linear sequences.
import BasicIS4.Syntax.HilbertLinear

-- Hilbert-style axiomatic formalisation of syntax.
import BasicIS4.Syntax.Hilbert

-- Gentzen-style natural deduction formalisation of syntax, after Bierman-de Paiva.
import BasicIS4.Syntax.Gentzen

-- Hilbert-style axiomatic formalisation of syntax with a separate modal context, as linear sequences.
import BasicIS4.Syntax.DyadicHilbertLinear

-- Hilbert-style axiomatic formalisation of syntax with a separate modal context.
import BasicIS4.Syntax.DyadicHilbert

-- Gentzen-style natural deduction formalisation of syntax with a separate modal context, after Pfenning-Davies.
import BasicIS4.Syntax.DyadicGentzen

-- Gentzen-style natural deduction formalisation of syntax with a separate relational context, after Basin-Matthews-Viganò.
import BasicIS4.Syntax.LabelledGentzen

-- Translation between different formalisations of syntax.
import BasicIS4.Syntax.Translation -- FIXME


-- Basic Kripke-style semantics, after Ono, for soundness only.
import BasicIS4.Semantics.BasicKripkeOno

-- Basic Kripke-style semantics, after Božić-Došen, for soundness only.
import BasicIS4.Semantics.BasicKripkeBozicDosen

-- Basic Kripke-style semantics, after Ewald, Servi, and Plotkin-Stirling, for soundness only.
import BasicIS4.Semantics.BasicKripkeEwald

-- Basic Kripke-style semantics, after Alechina-Mendler-de Paiva-Ritter, for soundness only.
import BasicIS4.Semantics.BasicKripkeAlechinaEtAl

-- Tarski-style semantics with implicit closed syntax representation, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiClosedGabbayNanevski

-- Tarski-style semantics with explicit Hilbert-style closed syntax representation.
import BasicIS4.Semantics.TarskiClosedHilbert

-- Tarski-style semantics with implicit syntax representation, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiGabbayNanevski

-- Tarski-style semantics with explicit Hilbert-style syntax representation.
import BasicIS4.Semantics.TarskiHilbert

-- Tarski-style semantics with explicit Gentzen-style syntax representation.
import BasicIS4.Semantics.TarskiGentzen

-- Tarski-style semantics with implicit syntax representation and a separate modal context, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiDyadicGabbayNanevski

-- Tarski-style semantics with explicit Hilbert-style syntax representation and a separate modal context.
import BasicIS4.Semantics.TarskiDyadicHilbert

-- Tarski-style semantics with explicit Gentzen-style syntax representation and a separate modal context.
import BasicIS4.Semantics.TarskiDyadicGentzen


-- Canonical and non-canonical model equipment for Kripke-style semantics.
import BasicIS4.Equipment.KripkeCanonical
import BasicIS4.Equipment.KripkeNonCanonical
import BasicIS4.Equipment.KripkeDyadicCanonical
import BasicIS4.Equipment.KripkeDyadicNonCanonical


import BasicIS4.Metatheory.ClosedHilbert-TarskiClosedGabbayNanevski
import BasicIS4.Metatheory.ClosedHilbert-TarskiClosedHilbert

import BasicIS4.Metatheory.Hilbert-BasicKripkeOno
import BasicIS4.Metatheory.Hilbert-BasicKripkeBozicDosen
import BasicIS4.Metatheory.Hilbert-BasicKripkeEwald
import BasicIS4.Metatheory.Hilbert-BasicKripkeAlechinaEtAl
import BasicIS4.Metatheory.Hilbert-TarskiClosedGabbayNanevski
import BasicIS4.Metatheory.Hilbert-TarskiClosedHilbert
import BasicIS4.Metatheory.Hilbert-TarskiGabbayNanevski
import BasicIS4.Metatheory.Hilbert-TarskiHilbert
import BasicIS4.Metatheory.Hilbert-TarskiGentzen

import BasicIS4.Metatheory.Gentzen-BasicKripkeOno
import BasicIS4.Metatheory.Gentzen-BasicKripkeBozicDosen
import BasicIS4.Metatheory.Gentzen-BasicKripkeEwald
import BasicIS4.Metatheory.Gentzen-BasicKripkeAlechinaEtAl
import BasicIS4.Metatheory.Gentzen-TarskiClosedGabbayNanevski
import BasicIS4.Metatheory.Gentzen-TarskiGabbayNanevski
import BasicIS4.Metatheory.Gentzen-TarskiGentzen

import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeOno
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeBozicDosen
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeEwald
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeAlechinaEtAl
import BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicGabbayNanevski
import BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicHilbert

import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeOno
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeBozicDosen
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeEwald
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeAlechinaEtAl
import BasicIS4.Metatheory.DyadicGentzen-TarskiDyadicGabbayNanevski
import BasicIS4.Metatheory.DyadicGentzen-TarskiDyadicGentzen




-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +. (To be rewritten.)

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
