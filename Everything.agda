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


-- Intuitionistic propositional calculus, without ∨ or ⊥.

import BasicIPC
import BasicIPC.TarskiSemantics
import BasicIPC.KripkeSemantics
import BasicIPC.Hilbert.List
import BasicIPC.Hilbert.ListWithContext
import BasicIPC.Hilbert.Tree
import BasicIPC.Hilbert.Tree.TarskiSoundness
import BasicIPC.Hilbert.Tree.TarskiBasicCompleteness
import BasicIPC.Hilbert.TreeWithContext
import BasicIPC.Hilbert.TreeWithContext.TarskiSoundness
import BasicIPC.Hilbert.TreeWithContext.KripkeSoundness
import BasicIPC.Hilbert.Translation
import BasicIPC.Gentzen
import BasicIPC.Gentzen.TarskiSoundness
import BasicIPC.Gentzen.KripkeSoundness
import BasicIPC.Gentzen.KripkeBasicCompleteness
import BasicIPC.Gentzen.KripkeCompleteness
import BasicIPC.Gentzen.HereditarySubstitution
import BasicIPC.Translation


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
import IPC.Hilbert.TreeWithContext.KripkeSoundness -- FIXME
import IPC.Hilbert.Translation
import IPC.Gentzen
import IPC.Gentzen.TarskiSoundness
import IPC.Gentzen.KripkeSoundness
import IPC.Gentzen.KripkeBasicCompleteness
import IPC.Gentzen.KripkeCompleteness
import IPC.Gentzen.HereditarySubstitution
import IPC.Translation


-- Intuitionistic modal logic S4, without ∨, ⊥, or ◇.

import BasicIS4
import BasicIS4.TarskiSemantics
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
import BasicIS4.Hilbert.TreeWithContext
import BasicIS4.Hilbert.TreeWithContext.TarskiSoundness -- FIXME
import BasicIS4.Hilbert.TreeWithContext.KripkeSoundness
import BasicIS4.Hilbert.TreeWithContextPair
import BasicIS4.Hilbert.TreeWithContextPair.TarskiSoundness -- FIXME
import BasicIS4.Hilbert.TreeWithContextPair.KripkeSoundness
import BasicIS4.Hilbert.Translation
import BasicIS4.Gentzen.TreeWithContext
import BasicIS4.Gentzen.TreeWithContext.TarskiSoundness -- FIXME
import BasicIS4.Gentzen.TreeWithContext.KripkeSoundness
import BasicIS4.Gentzen.TreeWithContext.KripkeEquipment
import BasicIS4.Gentzen.TreeWithContext.KripkeEquipmentToo
import BasicIS4.Gentzen.TreeWithContext.KripkeBasicCompleteness -- FIXME
import BasicIS4.Gentzen.TreeWithContextPair
import BasicIS4.Gentzen.TreeWithContextPair.TarskiSoundness -- FIXME
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
