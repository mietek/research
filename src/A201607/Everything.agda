-- An Agda formalisation of IPC, IS4, ICML, and ILP.  Work in progress.

module A201607.Everything where

import A201607.Common
import A201607.Common.Context
import A201607.Common.ContextPair
import A201607.Common.Predicate
import A201607.Common.PredicateBasedContext
import A201607.Common.Semantics
import A201607.Common.UntypedContext


--------------------------------------------------------------------------------

-- Basic intuitionistic propositional calculus, without ∨ or ⊥.


-- Common syntax.
import A201607.BasicIPC.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import A201607.BasicIPC.Syntax.ClosedHilbertSequential                          -- Sequences of terms.
import A201607.BasicIPC.Syntax.ClosedHilbert                                    -- Nested terms.

-- Hilbert-style formalisation of syntax.
import A201607.BasicIPC.Syntax.HilbertSequential                                -- Sequences of terms.
import A201607.BasicIPC.Syntax.Hilbert                                          -- Nested terms.

-- Gentzen-style formalisation of syntax.
import A201607.BasicIPC.Syntax.Gentzen                                          -- Simple terms.
import A201607.BasicIPC.Syntax.GentzenNormalForm                                -- Normal forms and neutrals.
import A201607.BasicIPC.Syntax.GentzenSpinalNormalForm                          -- Normal forms, neutrals, and spines.

-- Translation between different formalisations of syntax.
import A201607.BasicIPC.Syntax.Translation


-- Basic Tarski-style semantics, for soundness only.
import A201607.BasicIPC.Semantics.BasicTarski

-- Tarski-style semantics with glueing for α and ▻, after Coquand-Dybjer.
import A201607.BasicIPC.Semantics.TarskiGluedClosedImplicit                     -- Implicit closed syntax.
import A201607.BasicIPC.Semantics.TarskiGluedClosedHilbert                      -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import A201607.BasicIPC.Semantics.TarskiConcreteGluedImplicit                   -- Implicit syntax.
import A201607.BasicIPC.Semantics.TarskiConcreteGluedHilbert                    -- Hilbert-style syntax.
import A201607.BasicIPC.Semantics.TarskiConcreteGluedGentzen                    -- Gentzen-style syntax.

-- Kripke-style semantics with contexts as concrete worlds, and glueing for α and ▻.
import A201607.BasicIPC.Semantics.KripkeConcreteGluedImplicit                   -- Implicit syntax.
import A201607.BasicIPC.Semantics.KripkeConcreteGluedHilbert                    -- Hilbert-style syntax.
import A201607.BasicIPC.Semantics.KripkeConcreteGluedGentzen                    -- Gentzen-style syntax.

-- Kripke-style semantics with contexts as concrete worlds.
import A201607.BasicIPC.Semantics.KripkeConcrete

-- Kripke-style semantics with abstract worlds.
import A201607.BasicIPC.Semantics.KripkeMcKinseyTarski                          -- McKinsey-Tarski embedding.
import A201607.BasicIPC.Semantics.KripkeGodel                                   -- Gödel embedding.


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

import A201607.BasicIPC.Metatheory.ClosedHilbert-BasicTarski
import A201607.BasicIPC.Metatheory.ClosedHilbert-TarskiGluedClosedImplicit
import A201607.BasicIPC.Metatheory.ClosedHilbert-TarskiGluedClosedHilbert

import A201607.BasicIPC.Metatheory.Hilbert-BasicTarski
import A201607.BasicIPC.Metatheory.Hilbert-TarskiGluedClosedImplicit
import A201607.BasicIPC.Metatheory.Hilbert-TarskiGluedClosedHilbert
import A201607.BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedImplicit
import A201607.BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedHilbert
import A201607.BasicIPC.Metatheory.Hilbert-TarskiConcreteGluedGentzen
import A201607.BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedImplicit
import A201607.BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedHilbert
import A201607.BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedGentzen
import A201607.BasicIPC.Metatheory.Hilbert-KripkeConcrete
import A201607.BasicIPC.Metatheory.Hilbert-KripkeMcKinseyTarski
import A201607.BasicIPC.Metatheory.Hilbert-KripkeGodel

import A201607.BasicIPC.Metatheory.Gentzen-BasicTarski
import A201607.BasicIPC.Metatheory.Gentzen-TarskiGluedClosedImplicit
import A201607.BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedImplicit
import A201607.BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedHilbert
import A201607.BasicIPC.Metatheory.Gentzen-TarskiConcreteGluedGentzen
import A201607.BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedImplicit
import A201607.BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedHilbert
import A201607.BasicIPC.Metatheory.Gentzen-KripkeConcreteGluedGentzen
import A201607.BasicIPC.Metatheory.Gentzen-KripkeConcrete
import A201607.BasicIPC.Metatheory.Gentzen-KripkeMcKinseyTarski
import A201607.BasicIPC.Metatheory.Gentzen-KripkeGodel

import A201607.BasicIPC.Metatheory.GentzenNormalForm-KripkeConcrete
import A201607.BasicIPC.Metatheory.GentzenNormalForm-KripkeMcKinseyTarski
import A201607.BasicIPC.Metatheory.GentzenNormalForm-KripkeGodel

import A201607.BasicIPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution


--------------------------------------------------------------------------------

-- TODO


-- Common syntax.
import A201607.BasicT.Syntax.Common

-- Gentzen-style formalisation of syntax.
import A201607.BasicT.Syntax.Gentzen
import A201607.BasicT.Syntax.GentzenNormalForm

-- Basic Tarski-style semantics, for soundness only.
import A201607.BasicT.Semantics.BasicTarski


-- Available metatheory.

import A201607.BasicT.Metatheory.Gentzen-BasicTarski

import A201607.BasicT.Metatheory.GentzenNormalForm-Unknown


--------------------------------------------------------------------------------

-- Intuitionistic propositional calculus.


-- Common syntax.
import A201607.IPC.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import A201607.IPC.Syntax.ClosedHilbertSequential                               -- Sequences of terms.
import A201607.IPC.Syntax.ClosedHilbert                                         -- Nested terms.

-- Hilbert-style formalisation of syntax.
import A201607.IPC.Syntax.HilbertSequential                                     -- Sequences of terms.
import A201607.IPC.Syntax.Hilbert                                               -- Nested terms.

-- Gentzen-style formalisation of syntax.
import A201607.IPC.Syntax.Gentzen                                               -- Simple terms.
import A201607.IPC.Syntax.GentzenNormalForm                                     -- Normal forms and neutrals.
import A201607.IPC.Syntax.GentzenSpinalNormalForm                               -- Normal forms, neutrals, and spines.

-- Translation between different formalisations of syntax.
import A201607.IPC.Syntax.Translation


-- Basic Tarski-style semantics, for soundness only.
import A201607.IPC.Semantics.BasicTarski

-- Kripke-style semantics with exploding abstract worlds.
import A201607.IPC.Semantics.KripkeExploding


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

import A201607.IPC.Metatheory.ClosedHilbert-BasicTarski

import A201607.IPC.Metatheory.Hilbert-BasicTarski

import A201607.IPC.Metatheory.Gentzen-BasicTarski
import A201607.IPC.Metatheory.Gentzen-KripkeExploding

import A201607.IPC.Metatheory.GentzenNormalForm-KripkeExploding

import A201607.IPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution


--------------------------------------------------------------------------------

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.


-- Common syntax.
import A201607.BasicIS4.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
import A201607.BasicIS4.Syntax.ClosedHilbertSequential                          -- Sequences of terms.
import A201607.BasicIS4.Syntax.ClosedHilbert                                    -- Nested terms.

-- Hilbert-style formalisation of syntax.
import A201607.BasicIS4.Syntax.HilbertSequential                                -- Sequences of terms.
import A201607.BasicIS4.Syntax.Hilbert                                          -- Nested terms.

-- Gentzen-style formalisation of syntax, after Bierman-de Paiva.
import A201607.BasicIS4.Syntax.Gentzen

-- Hilbert-style formalisation of syntax with context pairs.
import A201607.BasicIS4.Syntax.DyadicHilbertSequential                          -- Sequences of terms.
import A201607.BasicIS4.Syntax.DyadicHilbert                                    -- Nested terms.

-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.
import A201607.BasicIS4.Syntax.DyadicGentzen                                    -- Simple terms.
import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm                          -- Normal forms and neutrals.
import A201607.BasicIS4.Syntax.DyadicGentzenSpinalNormalForm                    -- Normal forms, neutrals, and spines.

-- Gentzen-style formalisation of labelled syntax, after Basin-Matthews-Viganò.
import A201607.BasicIS4.Syntax.LabelledGentzen

-- Translation between different formalisations of syntax.
import A201607.BasicIS4.Syntax.Translation


-- Basic Kripke-style semantics with abstract worlds, for soundness only.
import A201607.BasicIS4.Semantics.BasicKripkeOno                                -- Ono-style conditions.
import A201607.BasicIS4.Semantics.BasicKripkeBozicDosen                         -- Božić-Došen-style conditions.
import A201607.BasicIS4.Semantics.BasicKripkeEwald                              -- Ewald-style conditions.
import A201607.BasicIS4.Semantics.BasicKripkeAlechina                           -- Alechina-style conditions.

-- Tarski-style semantics with glueing for α, ▻, and □, after Gabbay-Nanevski.
import A201607.BasicIS4.Semantics.TarskiClosedOvergluedImplicit                 -- Implicit closed syntax.
import A201607.BasicIS4.Semantics.TarskiClosedOvergluedHilbert                  -- Hilbert-style closed syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for α, ▻, and □.
import A201607.BasicIS4.Semantics.TarskiOvergluedImplicit                       -- Implicit syntax.
import A201607.BasicIS4.Semantics.TarskiOvergluedHilbert                        -- Hilbert-style syntax.
import A201607.BasicIS4.Semantics.TarskiOvergluedGentzen                        -- Gentzen-style syntax.

-- Tarski-style semantics with contexts as concrete worlds, and glueing for □ only.
import A201607.BasicIS4.Semantics.TarskiGluedImplicit                           -- Implicit syntax.
import A201607.BasicIS4.Semantics.TarskiGluedHilbert                            -- Hilbert-style syntax.
import A201607.BasicIS4.Semantics.TarskiGluedGentzen                            -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
import A201607.BasicIS4.Semantics.TarskiOvergluedDyadicImplicit                 -- Implicit syntax.
import A201607.BasicIS4.Semantics.TarskiOvergluedDyadicHilbert                  -- Hilbert-style syntax.
import A201607.BasicIS4.Semantics.TarskiOvergluedDyadicGentzen                  -- Gentzen-style syntax.

-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
import A201607.BasicIS4.Semantics.TarskiGluedDyadicImplicit                     -- Implicit syntax.

-- TODO
import A201607.BasicIS4.Semantics.TarskiGluedDyadicHilbert                      -- Hilbert-style syntax.

import A201607.BasicIS4.Semantics.TarskiGluedDyadicGentzen                      -- Gentzen-style syntax.


-- Canonical model equipment for Kripke-style semantics with contexts as concrete worlds.
import A201607.BasicIS4.Equipment.KripkeCanonical
import A201607.BasicIS4.Equipment.KripkeNonCanonical

-- Canonical model equipment for Kripke-style semantics with context pairs as concrete worlds.
import A201607.BasicIS4.Equipment.KripkeDyadicCanonical
import A201607.BasicIS4.Equipment.KripkeDyadicNonCanonical


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


import A201607.BasicIS4.Metatheory.ClosedHilbert-TarskiClosedOvergluedImplicit
import A201607.BasicIS4.Metatheory.ClosedHilbert-TarskiClosedOvergluedHilbert

import A201607.BasicIS4.Metatheory.Hilbert-BasicKripkeOno
import A201607.BasicIS4.Metatheory.Hilbert-BasicKripkeBozicDosen
import A201607.BasicIS4.Metatheory.Hilbert-BasicKripkeEwald
import A201607.BasicIS4.Metatheory.Hilbert-BasicKripkeAlechina
import A201607.BasicIS4.Metatheory.Hilbert-TarskiClosedOvergluedImplicit
import A201607.BasicIS4.Metatheory.Hilbert-TarskiClosedOvergluedHilbert
import A201607.BasicIS4.Metatheory.Hilbert-TarskiOvergluedImplicit
import A201607.BasicIS4.Metatheory.Hilbert-TarskiOvergluedHilbert
import A201607.BasicIS4.Metatheory.Hilbert-TarskiOvergluedGentzen
import A201607.BasicIS4.Metatheory.Hilbert-TarskiGluedImplicit
import A201607.BasicIS4.Metatheory.Hilbert-TarskiGluedHilbert

import A201607.BasicIS4.Metatheory.Gentzen-BasicKripkeOno
import A201607.BasicIS4.Metatheory.Gentzen-BasicKripkeBozicDosen
import A201607.BasicIS4.Metatheory.Gentzen-BasicKripkeEwald
import A201607.BasicIS4.Metatheory.Gentzen-BasicKripkeAlechina
import A201607.BasicIS4.Metatheory.Gentzen-TarskiClosedOvergluedImplicit
import A201607.BasicIS4.Metatheory.Gentzen-TarskiOvergluedImplicit
import A201607.BasicIS4.Metatheory.Gentzen-TarskiOvergluedGentzen
import A201607.BasicIS4.Metatheory.Gentzen-TarskiGluedImplicit -- FIXME
import A201607.BasicIS4.Metatheory.Gentzen-TarskiGluedGentzen -- FIXME

import A201607.BasicIS4.Metatheory.DyadicHilbert-BasicKripkeOno
import A201607.BasicIS4.Metatheory.DyadicHilbert-BasicKripkeBozicDosen
import A201607.BasicIS4.Metatheory.DyadicHilbert-BasicKripkeEwald
import A201607.BasicIS4.Metatheory.DyadicHilbert-BasicKripkeAlechina
import A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicImplicit
import A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicHilbert
import A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicGentzen
import A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicImplicit -- FIXME
import A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicHilbert

import A201607.BasicIS4.Metatheory.DyadicGentzen-BasicKripkeOno
import A201607.BasicIS4.Metatheory.DyadicGentzen-BasicKripkeBozicDosen
import A201607.BasicIS4.Metatheory.DyadicGentzen-BasicKripkeEwald
import A201607.BasicIS4.Metatheory.DyadicGentzen-BasicKripkeAlechina
import A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicImplicit
import A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicGentzen
import A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicImplicit -- FIXME
import A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicGentzen -- FIXME

import A201607.BasicIS4.Metatheory.DyadicGentzenSpinalNormalForm-HereditarySubstitution


--------------------------------------------------------------------------------

-- Basic intuitionistic contextual modal logic, without ∨ or ⊥.


-- Common syntax.
import A201607.BasicICML.Syntax.Common

-- Gentzen-style formalisation of syntax with context pairs, after Nanevski-Pfenning-Pientka.
import A201607.BasicICML.Syntax.DyadicGentzen
import A201607.BasicICML.Syntax.DyadicGentzenNormalForm
import A201607.BasicICML.Syntax.DyadicGentzenSpinalNormalForm

-- Available metatheory for basic ICML.
import A201607.BasicICML.Metatheory.DyadicGentzenSpinalNormalForm-HereditarySubstitution


--------------------------------------------------------------------------------

-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +.


-- Common syntax.
import A201607.BasicILP.Syntax.Common

-- Gentzen-style formalisation of syntax with context pairs.
import A201607.BasicILP.Syntax.DyadicGentzen
import A201607.BasicILP.Syntax.DyadicGentzenNormalForm


-- (To be rewritten.)

-- Common syntax, with types parametrised by a closed, untyped representation of syntax.
import A201607.OldBasicILP.UntypedSyntax.Common

-- Hilbert-style formalisation of closed syntax.
import A201607.OldBasicILP.UntypedSyntax.ClosedHilbertSequential                -- Sequences of terms.
import A201607.OldBasicILP.UntypedSyntax.ClosedHilbert                          -- Nested terms.

-- Translation between different formalisations of syntax.
import A201607.OldBasicILP.UntypedSyntax.Translation -- FIXME

-- Common syntax, with types parametrised by closed syntax.
import A201607.OldBasicILP.Syntax.Common

-- Hilbert-style formalisation of closed syntax.
-- import A201607.OldBasicILP.Syntax.ClosedHilbertSequential -- FIXME
-- import A201607.OldBasicILP.Syntax.ClosedHilbert -- FIXME

-- Translation between different formalisations of syntax.
-- import A201607.OldBasicILP.Syntax.Translation -- FIXME
-- import A201607.OldBasicILP.Syntax.Projection -- FIXME


-- (To be rewritten.)

import A201607.OlderBasicILP.Indirect
import A201607.OlderBasicILP.Indirect.Hilbert.Sequential
import A201607.OlderBasicILP.Indirect.Hilbert.Nested
import A201607.OlderBasicILP.Indirect.Gentzen
-- import A201607.OlderBasicILP.Indirect.Translation
import A201607.OlderBasicILP.Direct.Hilbert.Nested
import A201607.OlderBasicILP.Direct.Gentzen
-- import A201607.OlderBasicILP.Direct.Translation


--------------------------------------------------------------------------------

-- TODO: unfinished

import A201607.WIP.BasicIPC.Syntax.GentzenNormalForm2
import A201607.WIP.BasicIPC.Syntax.GentzenNormalFormN

import A201607.WIP.BasicIS4.Sketch

import A201607.WIP.BasicICML.Sketch

import A201607.WIP.BasicILP.Sketch

import A201607.WIP.Sketch


--------------------------------------------------------------------------------

-- TODO: unfinished

-- Kripke-style semantics with exploding abstract worlds, and glueing for □ only.
import A201607.WIP2.BasicIS4.Semantics.KripkeGluedExploding
import A201607.WIP2.BasicIS4.Semantics.Sketch
import A201607.WIP2.BasicIS4.Semantics.Sketch2
import A201607.WIP2.BasicIS4.Semantics.Sketch3
import A201607.WIP2.BasicIS4.Semantics.Sketch4
import A201607.WIP2.BasicIS4.Semantics.Sketch5
import A201607.WIP2.BasicIS4.Semantics.Sketch6
import A201607.WIP2.BasicIS4.Semantics.Sketch7
import A201607.WIP2.BasicIS4.Semantics.Sketch8
import A201607.WIP2.BasicIS4.Semantics.Sketch9
import A201607.WIP2.BasicIS4.Semantics.Sketch10

import A201607.WIP2.BasicIS4.Metatheory.DyadicGentzenNormalForm-TarskiGluedDyadicGentzen
import A201607.WIP2.BasicIS4.Metatheory.Sketch

import A201607.WIP2.BasicICML.Sketch
import A201607.WIP2.BasicICML.Sketch2


--------------------------------------------------------------------------------
