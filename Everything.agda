{-

https://github.com/mietek/hilbert-gentzen

An Agda formalisation of IPC, S4, and LP.  Work in progress.

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

-- Hilbert-style formalisation of closed syntax.
import BasicIPC.Syntax.ClosedHilbertLinear  -- Linear sequences of terms.
import BasicIPC.Syntax.ClosedHilbert        -- Nested terms.

-- Hilbert-style formalisation of syntax.
import BasicIPC.Syntax.HilbertLinear  -- Linear sequences of terms.
import BasicIPC.Syntax.Hilbert        -- Nested terms.

-- Gentzen-style formalisation of syntax.
import BasicIPC.Syntax.Gentzen                  -- Simple terms.
import BasicIPC.Syntax.GentzenNormalForm        -- Normal forms and neutrals.
import BasicIPC.Syntax.GentzenSpinalNormalForm  -- Normal forms, neutrals, and spines.

-- Translation between different formalisations of syntax.
import BasicIPC.Syntax.Translation


-- Basic Tarski-style semantics, for soundness only.
import BasicIPC.Semantics.BasicTarski

-- Tarski-style semantics with glueing for α and ▻, after Coquand-Dybjer.
import BasicIPC.Semantics.TarskiClosedCoquandDybjer  -- Implicit closed syntax.
import BasicIPC.Semantics.TarskiClosedHilbert        -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import BasicIPC.Semantics.TarskiCoquandDybjer  -- Implicit syntax.
import BasicIPC.Semantics.TarskiHilbert        -- Hilbert-style syntax.
import BasicIPC.Semantics.TarskiGentzen        -- Gentzen-style syntax.

-- Tarski-style semantics with contexts as concrete worlds.
import BasicIPC.Semantics.Tarski

-- Kripke-style semantics with abstract worlds.
import BasicIPC.Semantics.KripkeMcKinseyTarski  -- McKinsey-Tarski embedding.
import BasicIPC.Semantics.KripkeGodel           -- Gödel embedding.


-- Available metatheory for basic IPC.
--
--       ┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
--       │ BT  │ TCCD│ TCH │ TCD │ TH  │ TG  │ T   │ KMT │ KG  │
-- ┌─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CH  │  e₀ │ e₀q₀│ e₀q₀│     │     │     │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ H   │  e  │ eq₀ │ eq₀ │ eq  │ eq  │ eq~ │ eq  │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ G   │  e  │ eq₀ │     │ eq  │     │ eq  │ eq  │ eq  │ eq  │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ Gⁿᶠ │     │     │     │     │     │     │ eq  │ eq  │ eq  │
-- └─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness.
-- eq~  : Soundness and completeness, using syntax translation.


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
import BasicIS4.Syntax.ClosedHilbertLinear  -- Linear sequences of terms.
import BasicIS4.Syntax.ClosedHilbert        -- Nested terms.

-- Hilbert-style formalisation of syntax.
import BasicIS4.Syntax.HilbertLinear  -- Linear sequences of terms.
import BasicIS4.Syntax.Hilbert        -- Nested terms.

-- Gentzen-style formalisation of syntax, after Bierman-de Paiva.
import BasicIS4.Syntax.Gentzen

-- Hilbert-style formalisation of syntax with context pairs.
import BasicIS4.Syntax.DyadicHilbertLinear  -- Linear sequences of terms.
import BasicIS4.Syntax.DyadicHilbert        -- Linear sequences of terms.

-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.
import BasicIS4.Syntax.DyadicGentzen

-- Gentzen-style formalisation of labelled syntax, after Basin-Matthews-Viganò.
import BasicIS4.Syntax.LabelledGentzen

-- Translation between different formalisations of syntax.
import BasicIS4.Syntax.Translation


-- Basic Kripke-style semantics with abstract worlds, for soundness only.
import BasicIS4.Semantics.BasicKripkeOno           -- Ono-style conditions.
import BasicIS4.Semantics.BasicKripkeBozicDosen    -- Božić-Došen-style conditions.
import BasicIS4.Semantics.BasicKripkeEwald         -- Ewald-style conditions.
import BasicIS4.Semantics.BasicKripkeAlechinaEtAl  -- Alechina-style conditions.

-- Tarski-style semantics with glueing for α, ▻, and □, after Coquand-Dybjer and Gabbay-Nanevski.
import BasicIS4.Semantics.TarskiClosedGabbayNanevski  -- Implicit closed syntax.
import BasicIS4.Semantics.TarskiClosedHilbert         -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α, ▻, and □.
import BasicIS4.Semantics.TarskiGabbayNanevski  -- Implicit syntax.
import BasicIS4.Semantics.TarskiHilbert         -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiGentzen         -- Gentzen-style syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for □ only.
import BasicIS4.Semantics.Tarski   -- Implicit syntax.
import BasicIS4.Semantics.Tarski1  -- Hilbert-style syntax.
import BasicIS4.Semantics.Tarski2  -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
import BasicIS4.Semantics.TarskiDyadicGabbayNanevski  -- Implicit syntax.
import BasicIS4.Semantics.TarskiDyadicHilbert         -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiDyadicGentzen         -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
import BasicIS4.Semantics.TarskiDyadic   -- Implicit syntax.
import BasicIS4.Semantics.TarskiDyadic1  -- Hilbert-style syntax.
import BasicIS4.Semantics.TarskiDyadic2  -- Gentzen-style syntax.


-- Canonical model equipment for Kripke-style semantics with contexts as concrete worlds.
import BasicIS4.Equipment.KripkeCanonical
import BasicIS4.Equipment.KripkeNonCanonical

-- Canonical model equipment for Kripke-style semantics with context pairs as concrete worlds.
import BasicIS4.Equipment.KripkeDyadicCanonical
import BasicIS4.Equipment.KripkeDyadicNonCanonical


-- Available metatheory for basic IS4.
--
--       ┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
--       │ BKO │ BKBD│ BKE │ BKA&│ TCGN│ TCH │ TGN │ TH  │ TG  │ TDGN│ TDH │ TDG │
-- ┌─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CH  │     │     │     │     │ e₀q₀│ e₀q₀│     │     │     │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ H   │  e  │  e  │  e  │  e  │ eq₀ │ eq₀ │ eq  │ eq  │ eq~ │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ G   │  e  │  e  │  e  │  e  │ eq₀ │     │ eq  │     │ eq  │     │     │     │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ DH  │  e  │  e  │  e  │  e  │     │     │     │     │     │ eq  │ eq  │ eq~ │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ DG  │  e  │  e  │  e  │  e  │     │     │     │     │     │ eq  │     │ eq  │
-- └─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
--
-- e₀   : Soundness only, for closed terms only.
-- e₀q₀ : Soundness and completeness, for closed terms only.
-- e    : Soundness only.
-- eq₀  : Soundness, for all terms; completeness, for closed terms only.
-- eq   : Soundness and completeness.
-- eq~  : Soundness and completeness, using syntax translation.


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
import BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicGentzen

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
