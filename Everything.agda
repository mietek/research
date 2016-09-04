{-

https://github.com/mietek/hilbert-gentzen

An Agda formalisation of IPC, IS4, ICML, and ILP.  Work in progress.

Made by Miëtek Bak.  Published under the MIT X11 license.

-}

module Everything where

import Common
import Common.Context
import Common.ContextPair
import Common.Predicate
import Common.PredicateBasedContext
import Common.Semantics
import Common.UntypedContext




-- Basic intuitionistic propositional calculus, without ∨ or ⊥.


-- Common syntax.
import BasicIPC.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import BasicIPC.Syntax.ClosedHilbertSequential  -- Sequences of terms.
import BasicIPC.Syntax.ClosedHilbert            -- Nested terms.

-- Hilbert-style formalisation of syntax.
import BasicIPC.Syntax.HilbertSequential        -- Sequences of terms.
import BasicIPC.Syntax.Hilbert                  -- Nested terms.

-- Gentzen-style formalisation of syntax.
import BasicIPC.Syntax.Gentzen                  -- Simple terms.
import BasicIPC.Syntax.GentzenNormalForm        -- Normal forms and neutrals.
import BasicIPC.Syntax.GentzenSpinalNormalForm  -- Normal forms, neutrals, and spines.

-- Translation between different formalisations of syntax.
import BasicIPC.Syntax.Translation


-- Basic Tarski-style semantics, for soundness only.
import BasicIPC.Semantics.BasicTarski

-- Tarski-style semantics with glueing for α and ▻, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiClosedGluedImplicit  -- Implicit closed syntax.
import BasicIPC.Semantics.TarskiClosedGluedHilbert   -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import BasicIPC.Semantics.TarskiGluedImplicit        -- Implicit syntax.
import BasicIPC.Semantics.TarskiGluedHilbert         -- Hilbert-style syntax.
import BasicIPC.Semantics.TarskiGluedGentzen         -- Gentzen-style syntax.

-- Tarski-style semantics with contexts as concrete worlds.
import BasicIPC.Semantics.Tarski

-- Kripke-style semantics with abstract worlds.
import BasicIPC.Semantics.KripkeMcKinseyTarski       -- McKinsey-Tarski embedding.
import BasicIPC.Semantics.KripkeGodel                -- Gödel embedding.


-- Available metatheory for basic IPC.
--
--       ┌─────┬─────┬─────┬─────┐
--       │ CH  │ H   │ G   │ Gⁿᶠ │
-- ┌─────┼─────┼─────┼─────┼─────┤
-- │ BT  │ e₀  │ e   │ e   │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ TCGI│ e₀q₀│ eq₀ │ eq₀ │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ TCGH│ e₀q₀│ eq₀ │     │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ TGI │     │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ TGH │     │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ TGG │     │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ T   │     │ eq  │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ KMT │     │ eq  │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┤
-- │ KG  │     │ eq  │ eq  │ eq  │
-- └─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness.


import BasicIPC.Metatheory.ClosedHilbert-BasicTarski
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedGluedImplicit
import BasicIPC.Metatheory.ClosedHilbert-TarskiClosedGluedHilbert

import BasicIPC.Metatheory.Hilbert-BasicTarski
import BasicIPC.Metatheory.Hilbert-TarskiClosedGluedImplicit
import BasicIPC.Metatheory.Hilbert-TarskiClosedGluedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiGluedImplicit
import BasicIPC.Metatheory.Hilbert-TarskiGluedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiGluedGentzen
import BasicIPC.Metatheory.Hilbert-Tarski
import BasicIPC.Metatheory.Hilbert-KripkeMcKinseyTarski
import BasicIPC.Metatheory.Hilbert-KripkeGodel

import BasicIPC.Metatheory.Gentzen-BasicTarski
import BasicIPC.Metatheory.Gentzen-TarskiClosedGluedImplicit
import BasicIPC.Metatheory.Gentzen-TarskiGluedImplicit
import BasicIPC.Metatheory.Gentzen-TarskiGluedHilbert
import BasicIPC.Metatheory.Gentzen-TarskiGluedGentzen
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
import IPC.Hilbert.TreeWithContext.KripkeSoundness
import IPC.Hilbert.Translation
import IPC.Gentzen
import IPC.Gentzen.TarskiSoundness
import IPC.Gentzen.TarskiBasicCompleteness
import IPC.Gentzen.KripkeSoundness
import IPC.Gentzen.KripkeBasicCompleteness
import IPC.Gentzen.KripkeCompleteness
import IPC.Gentzen.HereditarySubstitution
import IPC.Translation




-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.


-- Common syntax.
import BasicIS4.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import BasicIS4.Syntax.ClosedHilbertSequential  -- Sequences of terms.
import BasicIS4.Syntax.ClosedHilbert            -- Nested terms.

-- Hilbert-style formalisation of syntax.
import BasicIS4.Syntax.HilbertSequential        -- Sequences of terms.
import BasicIS4.Syntax.Hilbert                  -- Nested terms.

-- Gentzen-style formalisation of syntax, after Bierman-de Paiva.
import BasicIS4.Syntax.Gentzen

-- Hilbert-style formalisation of syntax with context pairs.
import BasicIS4.Syntax.DyadicHilbertSequential  -- Sequences of terms.
import BasicIS4.Syntax.DyadicHilbert            -- Nested terms.

-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.
import BasicIS4.Syntax.DyadicGentzen

-- Gentzen-style formalisation of labelled syntax, after Basin-Matthews-Viganò.
import BasicIS4.Syntax.LabelledGentzen

-- Translation between different formalisations of syntax.
import BasicIS4.Syntax.Translation


-- Basic Kripke-style semantics with abstract worlds, for soundness only.
import BasicIS4.Semantics.BasicKripkeOno                 -- Ono-style conditions.
import BasicIS4.Semantics.BasicKripkeBozicDosen          -- Božić-Došen-style conditions.
import BasicIS4.Semantics.BasicKripkeEwald               -- Ewald-style conditions.
import BasicIS4.Semantics.BasicKripkeAlechina            -- Alechina-style conditions.

-- Tarski-style semantics with glueing for α, ▻, and □, after Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiClosedOvergluedImplicit  -- Implicit closed syntax.
import BasicIS4.Semantics.TarskiClosedOvergluedHilbert   -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α, ▻, and □.
import BasicIS4.Semantics.TarskiOvergluedImplicit        -- Implicit syntax.
import BasicIS4.Semantics.TarskiOvergluedHilbert         -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiOvergluedGentzen         -- Gentzen-style syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for □ only.
import BasicIS4.Semantics.TarskiGluedImplicit            -- Implicit syntax.
import BasicIS4.Semantics.TarskiGluedHilbert             -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiGluedGentzen             -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
import BasicIS4.Semantics.TarskiOvergluedDyadicImplicit  -- Implicit syntax.
import BasicIS4.Semantics.TarskiOvergluedDyadicHilbert   -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiOvergluedDyadicGentzen   -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
import BasicIS4.Semantics.TarskiGluedDyadicImplicit      -- Implicit syntax.

-- TODO
import BasicIS4.Semantics.TarskiGluedDyadicHilbert       -- Hilbert-style syntax.

import BasicIS4.Semantics.TarskiGluedDyadicGentzen       -- Gentzen-style syntax.


-- Canonical model equipment for Kripke-style semantics with contexts as concrete worlds.
import BasicIS4.Equipment.KripkeCanonical
import BasicIS4.Equipment.KripkeNonCanonical

-- Canonical model equipment for Kripke-style semantics with context pairs as concrete worlds.
import BasicIS4.Equipment.KripkeDyadicCanonical
import BasicIS4.Equipment.KripkeDyadicNonCanonical


-- Available metatheory for basic IS4.
--
--       ┌─────┬─────┬─────┬─────┬─────┐
--       │ CH  │ H   │ G   │ DH  │ DG  │
-- ┌─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BKO │     │ e   │ e   │ e   │ e   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BKBD│     │ e   │ e   │ e   │ e   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BKE │     │ e   │ e   │ e   │ e   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BKA&│     │ e   │ e   │ e   │ e   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TCOI│ e₀q₀│ eq₀ │ eq₀ │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TCOH│ e₀q₀│ eq₀ │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TOI │     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TOH │     │ eq  │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TOG │     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGI │     │ eq  │ WIP │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGH │     │ eq  │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGG │     │     │ WIP │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TODI│     │     │     │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TODH│     │     │     │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TODG│     │     │     │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGDI│     │     │     │ WIP │ WIP │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGDH│     │     │     │ WIP │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGDG│     │     │     │     │ WIP │
-- └─────┴─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness.
-- WIP  : Work in progress.


import BasicIS4.Metatheory.ClosedHilbert-TarskiClosedOvergluedImplicit
import BasicIS4.Metatheory.ClosedHilbert-TarskiClosedOvergluedHilbert

import BasicIS4.Metatheory.Hilbert-BasicKripkeOno
import BasicIS4.Metatheory.Hilbert-BasicKripkeBozicDosen
import BasicIS4.Metatheory.Hilbert-BasicKripkeEwald
import BasicIS4.Metatheory.Hilbert-BasicKripkeAlechina
import BasicIS4.Metatheory.Hilbert-TarskiClosedOvergluedImplicit
import BasicIS4.Metatheory.Hilbert-TarskiClosedOvergluedHilbert
import BasicIS4.Metatheory.Hilbert-TarskiOvergluedImplicit
import BasicIS4.Metatheory.Hilbert-TarskiOvergluedHilbert
import BasicIS4.Metatheory.Hilbert-TarskiOvergluedGentzen
import BasicIS4.Metatheory.Hilbert-TarskiGluedImplicit
import BasicIS4.Metatheory.Hilbert-TarskiGluedHilbert

import BasicIS4.Metatheory.Gentzen-BasicKripkeOno
import BasicIS4.Metatheory.Gentzen-BasicKripkeBozicDosen
import BasicIS4.Metatheory.Gentzen-BasicKripkeEwald
import BasicIS4.Metatheory.Gentzen-BasicKripkeAlechina
import BasicIS4.Metatheory.Gentzen-TarskiClosedOvergluedImplicit
import BasicIS4.Metatheory.Gentzen-TarskiOvergluedImplicit
import BasicIS4.Metatheory.Gentzen-TarskiOvergluedGentzen
import BasicIS4.Metatheory.Gentzen-TarskiGluedImplicit -- FIXME
import BasicIS4.Metatheory.Gentzen-TarskiGluedGentzen -- FIXME

import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeOno
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeBozicDosen
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeEwald
import BasicIS4.Metatheory.DyadicHilbert-BasicKripkeAlechina
import BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicImplicit
import BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicHilbert
import BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicGentzen
import BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicImplicit -- FIXME
import BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicHilbert

import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeOno
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeBozicDosen
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeEwald
import BasicIS4.Metatheory.DyadicGentzen-BasicKripkeAlechina
import BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicImplicit
import BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicGentzen
import BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicImplicit -- FIXME
import BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicGentzen -- FIXME




-- Basic intuitionistic contextual modal logic, without ∨ or ⊥.

-- Common syntax.
import BasicICML.Syntax.Common

-- Gentzen-style formalisation of syntax with context pairs, after Nanevski-Pfenning-Pientka.
import BasicICML.Syntax.DyadicGentzen




-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +. (Work in progress.)

-- Common syntax, with types parametrised by a closed, untyped representation of syntax.
import OldBasicILP.UntypedSyntax.Common

-- Hilbert-style formalisation of closed syntax.
import OldBasicILP.UntypedSyntax.ClosedHilbertSequential  -- Sequences of terms.
import OldBasicILP.UntypedSyntax.ClosedHilbert            -- Nested terms.

-- Translation between different formalisations of syntax.
import OldBasicILP.UntypedSyntax.Translation -- FIXME

-- Common syntax, with types parametrised by closed syntax.
import OldBasicILP.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import OldBasicILP.Syntax.ClosedHilbertSequential  -- Sequences of terms.
import OldBasicILP.Syntax.ClosedHilbert            -- Nested terms.

-- Translation between different formalisations of syntax.
import OldBasicILP.Syntax.Translation -- FIXME
-- import OldBasicILP.Syntax.Projection -- FIXME


-- (To be rewritten.)

import OlderBasicILP.Indirect
import OlderBasicILP.Indirect.Hilbert.Sequential
import OlderBasicILP.Indirect.Hilbert.Nested
import OlderBasicILP.Indirect.Gentzen
-- import OlderBasicILP.Indirect.Translation
import OlderBasicILP.Direct.Hilbert.Nested
import OlderBasicILP.Direct.Gentzen
-- import OlderBasicILP.Direct.Translation
