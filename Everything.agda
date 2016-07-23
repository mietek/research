module Everything where

import Common
import Common.Context


-- Intuitionistic propositional calculus, without ∨ or ⊥.

import BasicIPC
import BasicIPC.TarskiSemantics
import BasicIPC.KripkeSemantics
import BasicIPC.Hilbert.Sequential
import BasicIPC.Hilbert.Nested
import BasicIPC.Hilbert.Nested.TarskiSoundness
import BasicIPC.Hilbert.Nested.KripkeSoundness
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
import IPC.Hilbert.Sequential
import IPC.Hilbert.Nested
import IPC.Hilbert.Nested.TarskiSoundness
-- import IPC.Hilbert.Nested.KripkeSoundness
import IPC.Gentzen
import IPC.Gentzen.TarskiSoundness
import IPC.Gentzen.KripkeSoundness
import IPC.Gentzen.KripkeBasicCompleteness
import IPC.Gentzen.KripkeCompleteness
import IPC.Gentzen.HereditarySubstitution
import IPC.Translation


-- Intuitionistic modal logic S4, without ∨, ⊥, or ◇.

import BasicIS4
import BasicIS4.KripkeSemantics.Ono
import BasicIS4.KripkeSemantics.BozicDosen
import BasicIS4.KripkeSemantics.Wijesekera
import BasicIS4.KripkeSemantics.EwaldEtAl
import BasicIS4.KripkeSemantics.AlechinaEtAl
import BasicIS4.Regular.Hilbert.Sequential
import BasicIS4.Regular.Hilbert.Nested
import BasicIS4.Regular.Hilbert.KripkeSoundness
import BasicIS4.Regular.Gentzen
import BasicIS4.Regular.Gentzen.KripkeSoundness
import BasicIS4.Regular.Gentzen.KripkeBasicCompleteness -- FIXME
import BasicIS4.Regular.Translation
import BasicIS4.DualContext.Hilbert.Sequential
import BasicIS4.DualContext.Hilbert.Nested
import BasicIS4.DualContext.Gentzen
import BasicIS4.DualContext.Translation
import BasicIS4.Labelled.Gentzen
import BasicIS4.Translation


-- Intuitionistic logic of proofs, without ∨, ⊥, or +.

import BasicILP.Indirect
-- import BasicILP.Indirect.Hilbert.Sequential
import BasicILP.Indirect.Hilbert.Sequential
import BasicILP.Indirect.Hilbert.Nested
import BasicILP.Indirect.Gentzen
-- import BasicILP.Indirect.Translation
-- import BasicILP.Direct.Hilbert.Sequential
import BasicILP.Direct.Hilbert.Sequential
import BasicILP.Direct.Hilbert.Nested
import BasicILP.Direct.Gentzen
-- import BasicILP.Direct.Translation
-- import BasicILP.Translation
import BasicILP.Translation