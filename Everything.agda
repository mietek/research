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

-- Kripke-style possible worlds semantics, based on the Gödel translation.
import New.BasicIPC.Semantics.Kripke.Godel

-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.
import New.BasicIPC.Semantics.Kripke.McKinseyTarski


import New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.Basic
import New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.CoquandDybjer

import New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.Basic
import New.BasicIPC.Metatheory.Open.HilbertTree.Tarski.CoquandDybjer
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


-- Intuitionistic modal logic S4, without ∨, ⊥, or ◇.

import BasicIS4
import BasicIS4.TarskiSemantics
import BasicIS4.OpenSyntaxSemantics
import BasicIS4.KripkeSemantics
import BasicIS4.KripkeSemantics.Ono
import BasicIS4.KripkeSemantics.BozicDosen
import BasicIS4.KripkeSemantics.EwaldEtAl
import BasicIS4.KripkeSemantics.AlechinaEtAl
import BasicIS4.Hilbert.List
import BasicIS4.Hilbert.ListWithContext
import BasicIS4.Hilbert.ListWithContextPair
import BasicIS4.Hilbert.Tree
import BasicIS4.Hilbert.Tree.TarskiSoundness
import BasicIS4.Hilbert.Tree.TarskiBasicCompleteness
import BasicIS4.Hilbert.Tree.OpenSyntaxSoundness
import BasicIS4.Hilbert.Tree.OpenSyntaxBasicCompleteness
import BasicIS4.Hilbert.TreeWithContext
import BasicIS4.Hilbert.TreeWithContext.TarskiSoundness
import BasicIS4.Hilbert.TreeWithContext.TarskiBasicCompleteness
import BasicIS4.Hilbert.TreeWithContext.OpenSyntaxSoundness
import BasicIS4.Hilbert.TreeWithContext.OpenSyntaxBasicCompleteness -- FIXME
import BasicIS4.Hilbert.TreeWithContext.KripkeSoundness
import BasicIS4.Hilbert.TreeWithContextPair
import BasicIS4.Hilbert.TreeWithContextPair.TarskiSoundness -- FIXME
import BasicIS4.Hilbert.TreeWithContextPair.TarskiBasicCompleteness
import BasicIS4.Hilbert.TreeWithContextPair.OpenSyntaxSoundness
import BasicIS4.Hilbert.TreeWithContextPair.OpenSyntaxBasicCompleteness -- FIXME
import BasicIS4.Hilbert.TreeWithContextPair.KripkeSoundness
import BasicIS4.Hilbert.Translation
import BasicIS4.Gentzen.TreeWithContext
import BasicIS4.Gentzen.TreeWithContext.TarskiSoundness -- FIXME
import BasicIS4.Gentzen.TreeWithContext.TarskiBasicCompleteness
import BasicIS4.Gentzen.TreeWithContext.OpenSyntaxSoundness -- FIXME
import BasicIS4.Gentzen.TreeWithContext.KripkeSoundness
import BasicIS4.Gentzen.TreeWithContext.KripkeEquipment
import BasicIS4.Gentzen.TreeWithContext.KripkeEquipmentToo
import BasicIS4.Gentzen.TreeWithContext.KripkeBasicCompleteness -- FIXME
import BasicIS4.Gentzen.TreeWithContextPair
import BasicIS4.Gentzen.TreeWithContextPair.TarskiSoundness -- FIXME
import BasicIS4.Gentzen.TreeWithContextPair.TarskiBasicCompleteness
import BasicIS4.Gentzen.TreeWithContextPair.OpenSyntaxSoundness -- FIXME
import BasicIS4.Gentzen.TreeWithContextPair.KripkeSoundness
import BasicIS4.Gentzen.TreeWithContextPair.KripkeEquipment
import BasicIS4.Gentzen.TreeWithContextPair.KripkeEquipmentToo
import BasicIS4.Gentzen.TreeWithContextPair.KripkeBasicCompleteness -- FIXME
import BasicIS4.Gentzen.LabelledTreeWithContextPair -- FIXME
import BasicIS4.Gentzen.Translation
import BasicIS4.Translation


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
