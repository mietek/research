---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-H and BS-H
--
--                 7.1
--    SS-CBN|SS-H₂ ← SS-H ⎫     SS-H      ⎫   SS-H
--  1.1 ↓      ↓ 7.2       ⎬ 7.4 ↓ × ↑ 7.5 ⎬ 7.6 ↕
--    BS-CBN|BS-H₂ → BS-H ⎭     BS-H      ⎭   BS-H
--                 7.3

module Equivalence-H where

open import Syntax-Predicates
import Semantics-SmallStep as SS
import Semantics-BigStep as BS
import Properties-SmallStep-CBN as SS-CBN
import Properties-SmallStep-H as SS-H
-- import Properties-SmallStep-H₂ as SS-H₂
import Properties-BigStep-CBN as BS-CBN
import Properties-BigStep-H as BS-H
-- import Properties-BigStep-H₂ as BS-H₂
import Equivalence-CBN as CBN


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 7.1.  SS-H to HNF implies SS-CBN to WHNF followed by SS-H₂ to HNF

module Lem-7-1 where
  open SS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 7.2.  SS-H₂ to HNF implies BS-H₂

module Lem-7-2 where
--  open SS-H₂
--  open BS-H₂


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 7.3.  BS-CBN followed by BS-H₂ implies BS-H

module Lem-7-3 where
  open BS


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 7.4.  SS-H to HNF implies BS-H

module Cor-7-4 where
  open SS-H
  open BS-H


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 7.5.  BS-H implies SS-H

module Lem-2-5 where
  open SS-H
  open BS-H


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 7.6.  SS-H to HNF and BS-H coincide

module Thm-7-6 where
--  ss-h↔bs-h : ∀ {n} {e : Tm n} {e′} → (e SS.H.⇒* e′ × HNF e′) ↔ e BS.H.⇓ e′
--  ss-h↔bs-h = uncurry Cor-7-4.bs←ss , λ r → Lem-7-5.ss←bs r , BS-H.hnf-⇓ r


---------------------------------------------------------------------------------------------------------------
