{-

References

• N. Alechina, M. Mendler, V. de Paiva, E. Ritter (2001)
  “Categorical and Kripke semantics for constructive S4 modal logic”
  http://dx.doi.org/10.1007/3-540-44802-0_21

• A. Abel, J. Chapman (2014)
  “Normalization by evaluation in the delay monad”
  http://dx.doi.org/10.4204/EPTCS.153.4

• D. Basin, S. Matthews, L. Viganò (1997)
  “Labelled propositional modal logics: theory and practice”
  http://dx.doi.org/10.1093/logcom/7.6.685

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

• A. Stump (2016)
  “Verified functional programming in Agda”
  http://dx.doi.org/10.1145/2841316

-}

module README where

import Common.Core
import Common.Context

import BasicIPC.Core
import BasicIPC.Hilbert.Sequential
import BasicIPC.Hilbert.Nested
import BasicIPC.Gentzen.Core
import BasicIPC.Gentzen.TarskiSemantics
import BasicIPC.Gentzen.KripkeSemantics.Core
import BasicIPC.Gentzen.KripkeSemantics.BasicCompleteness
import BasicIPC.Gentzen.KripkeSemantics.Completeness
import BasicIPC.Gentzen.HereditarySubstitution
import BasicIPC.Translation

import IPCWithDisjunction.Core
import IPCWithDisjunction.Hilbert.Sequential
import IPCWithDisjunction.Hilbert.Nested
import IPCWithDisjunction.Gentzen.Core
import IPCWithDisjunction.Gentzen.TarskiSemantics
import IPCWithDisjunction.Gentzen.KripkeSemantics.Core
import IPCWithDisjunction.Gentzen.KripkeSemantics.BasicCompleteness
import IPCWithDisjunction.Gentzen.KripkeSemantics.Completeness
import IPCWithDisjunction.Translation

import IPCWithDisjunctionAndFalsehood.Core
import IPCWithDisjunctionAndFalsehood.Hilbert.Sequential
import IPCWithDisjunctionAndFalsehood.Hilbert.Nested
import IPCWithDisjunctionAndFalsehood.Gentzen.Core
import IPCWithDisjunctionAndFalsehood.Gentzen.TarskiSemantics
import IPCWithDisjunctionAndFalsehood.Gentzen.KripkeSemantics.Core
import IPCWithDisjunctionAndFalsehood.Gentzen.KripkeSemantics.BasicCompleteness
import IPCWithDisjunctionAndFalsehood.Gentzen.KripkeSemantics.Completeness
import IPCWithDisjunctionAndFalsehood.Translation

import IS4.Core
import IS4.Dual.Hilbert.Sequential
import IS4.Dual.Hilbert.Nested
import IS4.Dual.Gentzen
import IS4.Dual.Translation
-- import IS4.Dual.Semantics.KripkeWIP
import IS4.Labelled.Gentzen
-- import IS4.TranslationWIP
