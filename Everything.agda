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
import BasicIPC.Semantics.TarskiGluedClosedImplicit    -- Implicit closed syntax.
import BasicIPC.Semantics.TarskiGluedClosedHilbert     -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import BasicIPC.Semantics.TarskiConcreteGluedImplicit  -- Implicit syntax.
import BasicIPC.Semantics.TarskiConcreteGluedHilbert   -- Hilbert-style syntax.
import BasicIPC.Semantics.TarskiConcreteGluedGentzen   -- Gentzen-style syntax.

-- Kripke-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import BasicIPC.Semantics.KripkeConcreteGluedImplicit  -- Implicit syntax.
import BasicIPC.Semantics.KripkeConcreteGluedHilbert   -- Hilbert-style syntax.
import BasicIPC.Semantics.KripkeConcreteGluedGentzen   -- Gentzen-style syntax.

-- Kripke-style semantics with contexts as concrete worlds.
import BasicIPC.Semantics.KripkeConcrete

-- Kripke-style semantics with abstract worlds.
import BasicIPC.Semantics.KripkeMcKinseyTarski         -- McKinsey-Tarski embedding.
import BasicIPC.Semantics.KripkeGodel                  -- Gödel embedding.


-- Available metatheory for basic IPC.
--
--       ┌─────┬─────┬─────┬─────┬─────┐
--       │ CH  │ H   │ G   │ Gⁿᶠ │ Gˢⁿᶠ│
-- ┌─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BT  │ e₀  │ e   │ e   │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGCI│ e₀q₀│ eq₀ │ eq₀ │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TGCH│ e₀q₀│ eq₀ │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TCGI│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TCGH│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ TCGG│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KCGI│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KCGH│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KCGG│     │ eq  │ eq  │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KC  │     │ eq  │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KMT │     │ eq  │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KG  │     │ eq  │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ HS  │     │     │     │     │ n   │
-- └─────┴─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness, or normalisation by evaluation.
-- n    : Normalisation by other means.


import BasicIPC.Metatheory.ClosedHilbert-BasicTarski
import BasicIPC.Metatheory.ClosedHilbert-TarskiGluedClosedImplicit
import BasicIPC.Metatheory.ClosedHilbert-TarskiGluedClosedHilbert

import BasicIPC.Metatheory.Hilbert-BasicTarski
import BasicIPC.Metatheory.Hilbert-TarskiGluedClosedImplicit
import BasicIPC.Metatheory.Hilbert-TarskiGluedClosedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedImplicit
import BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedHilbert
import BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedGentzen
import BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedImplicit
import BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedHilbert
import BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedGentzen
import BasicIPC.Metatheory.Hilbert-KripkeConcrete
import BasicIPC.Metatheory.Hilbert-KripkeMcKinseyTarski
import BasicIPC.Metatheory.Hilbert-KripkeGodel

import BasicIPC.Metatheory.Gentzen-BasicTarski
import BasicIPC.Metatheory.Gentzen-TarskiGluedClosedImplicit
import BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedImplicit
import BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedHilbert
import BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedGentzen
import BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedImplicit
import BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedHilbert
import BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedGentzen
import BasicIPC.Metatheory.Gentzen-KripkeConcrete
import BasicIPC.Metatheory.Gentzen-KripkeMcKinseyTarski
import BasicIPC.Metatheory.Gentzen-KripkeGodel

import BasicIPC.Metatheory.GentzenNormalForm-KripkeConcrete
import BasicIPC.Metatheory.GentzenNormalForm-KripkeMcKinseyTarski
import BasicIPC.Metatheory.GentzenNormalForm-KripkeGodel

import BasicIPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution




-- TODO


-- Common syntax.
import BasicT.Syntax.Common

-- Gentzen-style formalisation of syntax.
import BasicT.Syntax.Gentzen
import BasicT.Syntax.GentzenNormalForm


-- Basic Tarski-style semantics, for soundness only.
import BasicT.Semantics.BasicTarski


-- Available metatheory.

import BasicT.Metatheory.Gentzen-BasicTarski

import BasicT.Metatheory.GentzenNormalForm-Unknown




-- Intuitionistic propositional calculus.


-- Common syntax.
import IPC.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import IPC.Syntax.ClosedHilbertSequential  -- Sequences of terms.
import IPC.Syntax.ClosedHilbert            -- Nested terms.

-- Hilbert-style formalisation of syntax.
import IPC.Syntax.HilbertSequential        -- Sequences of terms.
import IPC.Syntax.Hilbert                  -- Nested terms.

-- Gentzen-style formalisation of syntax.
import IPC.Syntax.Gentzen                  -- Simple terms.
import IPC.Syntax.GentzenNormalForm        -- Normal forms and neutrals.
import IPC.Syntax.GentzenSpinalNormalForm  -- Normal forms, neutrals, and spines.

-- Translation between different formalisations of syntax.
import IPC.Syntax.Translation


-- Basic Tarski-style semantics, for soundness only.
import IPC.Semantics.BasicTarski

-- Kripke-style semantics with exploding abstract worlds.
import IPC.Semantics.KripkeExploding


-- Available metatheory for IPC.
--
--       ┌─────┬─────┬─────┬─────┬─────┐
--       │ CH  │ H   │ G   │ Gⁿᶠ │ Gˢⁿᶠ│
-- ┌─────┼─────┼─────┼─────┼─────┼─────┤
-- │ BT  │ e₀  │ e   │ e   │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ KE  │     │     │ eq  │ eq  │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┤
-- │ HS  │     │     │     │     │ n   │
-- └─────┴─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness, or normalisation by evaluation.
-- n    : Normalisation by other means.

import IPC.Metatheory.ClosedHilbert-BasicTarski

import IPC.Metatheory.Hilbert-BasicTarski

import IPC.Metatheory.Gentzen-BasicTarski
import IPC.Metatheory.Gentzen-KripkeExploding

import IPC.Metatheory.GentzenNormalForm-KripkeExploding

import IPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution




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
-- eq   : Soundness and completeness, or normalisation by evaluation.
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




-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +.

-- Common syntax.
import BasicILP.Syntax.Common

-- Gentzen-style formalisation of syntax with context pairs.
import BasicILP.Syntax.DyadicGentzen


-- (To be rewritten.)

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
