---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HNO and BS-HNO
--
--                  8.1
--    SS-HS|SS-HNO₂ ← SS-HNO ⎫     SS-HNO    ⎫   SS-HNO
--  6.1 ↓     ↓ 8.2           ⎬ 8.4 ↓ × ↑ 8.5 ⎬ 8.6 ↕
--    BS-HS|BS-HNO₂ → BS-HNO ⎭     BS-HNO    ⎭   BS-HNO
--                  8.3

module 4-8-Equivalence-HNO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-6-Properties-SmallStep-HS as SS-HS
import 2-8-1-Properties-SmallStep-HNO as SS-HNO
-- import 2-8-2-Properties-SmallStep-HNO₂ as SS-HNO₂
import 3-6-Properties-BigStep-HS as BS-HS
import 3-8-1-Properties-BigStep-HNO as BS-HNO
-- import 3-8-2-Properties-BigStep-HNO₂ as BS-HNO₂
import 4-6-Equivalence-HS as HS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 8.1.  SS-HNO to NF implies SS-HS to HNF followed by SS-HNO₂ to NF

module Lem-8-1 where
  open SS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 8.2.  SS-HNO₂ to NF implies BS-HNO₂

module Lem-8-2 where
--  open SS-HNO₂
--  open BS-HNO₂


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 8.3.  BS-HS followed by BS-HNO₂ implies BS-HNO

module Lem-8-3 where
  open BS


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 8.4.  SS-HNO to NF implies BS-HNO

module Cor-8-4 where
  open SS-HNO
  open BS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 8.5.  BS-HNO implies SS-HNO

module Lem-2-5 where
  open SS-HNO
  open BS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 8.6.  SS-HNO to NF and BS-HNO coincide

module Thm-8-6 where
--  ss-hno↔bs-hno : ∀ {n} {e : Tm n} {e′} → (e SS.HNO.⇒* e′ × NF e′) ↔ e BS.HNO.⇓ e′
--  ss-hno↔bs-hno = uncurry Cor-8-4.bs←ss , λ r → Lem-8-5.ss←bs r , BS-HNO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
