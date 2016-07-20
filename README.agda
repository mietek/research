{-

References

• N. Alechina, M. Mendler, V. de Paiva, E. Ritter (2001)
  “Categorical and Kripke semantics for constructive S4 modal logic”
  http://dx.doi.org/10.1007/3-540-44802-0_21
  Extended version with proofs:
  http://www.cs.nott.ac.uk/~psznza/papers/Alechina++:01a.pdf

• A. Abel, J. Chapman (2014)
  “Normalization by evaluation in the delay monad”
  http://dx.doi.org/10.4204/EPTCS.153.4

• D. Basin, S. Matthews, L. Viganò (1997)
  “Labelled propositional modal logics: theory and practice”
  http://dx.doi.org/10.1093/logcom/7.6.685

• G. Bierman, V. de Paiva (2000)
  “On an intuitionistic modal logic”
  http://dx.doi.org/10.1023/A:1005291931660

• J. Chapman (2008)
  “Type checking and normalisation”
  http://jmchapman.github.io/papers/thesis.pdf

• R. Davies, F. Pfenning (2001)
  “A modal analysis of staged computation”
  http://dx.doi.org/10.1145/382780.382785

• R. Hakli, S. Negri (2010)
  “Does the deduction theorem fail for modal logic?”
  http://dx.doi.org/10.1007/s11229-011-9905-9

• D. Ilik (2010)
  “Continuation-passing style models complete for intuitionistic logic”
  http://dx.doi.org/10.1016/j.apal.2012.05.003

• F. Joachimski, R. Matthes (2003)
  “Short proofs of normalization for the simply-typed λ-calculus,
  permutative conversions and Gödel’s T”
  http://dx.doi.org/10.1007/s00153-002-0156-9

• C. Keller, T. Altenkirch (2010)
  “Hereditary substitutions for simple types, formalized”
  http://dx.doi.org/10.1145/1863597.1863601

• J. Malakhovski (2012)
  “Reinventing formal logic”
  http://oxij.org/note/ReinventingFormalLogic

• M. Marti, T. Studer (submitted 2016)
  “Intuitionistic modal logic made explicit”
  http://www.iam.unibe.ch/ltgpub/2016/mast16.pdf

• C. McBride (2013)
  “Dependently typed metaprogramming (in Agda)”
  https://github.com/pigworker/MetaprogAgda

• H. Ono (1977)
  “On some intuitionistic modal logics”
  http://dx.doi.org/10.2977/prims/1195189604

• F. Pfenning, R. Davies (2001)
  “A judgmental reconstruction of modal logic”
  http://dx.doi.org/10.1017/S0960129501003322

• F. Pfenning (2010)
  “Lecture notes on modal logic”
  http://www.cs.cmu.edu/~fp/courses/15816-s10

• A. Simpson (1994)
  “The proof theory and semantics of intuitionistic modal logic”
  http://homepages.inf.ed.ac.uk/als/Research/thesis.pdf

• A. Stump (2016)
  “Verified functional programming in Agda”
  http://dx.doi.org/10.1145/2841316

-}

module README where

import Common
import Common.Context


-- Intuitionistic propositional calculus, without ∨ or ⊥.

import BasicIPC
import BasicIPC.TarskiSemantics
import BasicIPC.KripkeSemantics
import BasicIPC.Hilbert.Sequential
import BasicIPC.Hilbert.Nested
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
