---------------------------------------------------------------------------------------------------------------
--
-- A formalisation of big-step and small-step operational semantics for λ-calculus

module 0-0-Everything where

open import 0-1-Prelude
open import 0-2-GenericEquipment

open import 1-1-Syntax-Terms
open import 1-2-Syntax-Predicates

import 2-1-Semantics-BigStep as BS
import 2-2-Semantics-SmallStep as SS

import 3-1-Properties-BigStep-CBN
import 3-2-1-Properties-BigStep-NO
import 3-2-2-Properties-BigStep-NO₂
import 3-3-Properties-BigStep-CBV
import 3-4-Properties-BigStep-AO
import 3-5-Properties-BigStep-HAO
import 3-6-Properties-BigStep-HS
import 3-7-1-Properties-BigStep-H
import 3-7-2-Properties-BigStep-H₂
import 3-8-1-Properties-BigStep-HNO
import 3-8-2-Properties-BigStep-HNO₂

import 4-1-Properties-SmallStep-CBN
import 4-2-1-Properties-SmallStep-NO
import 4-2-2-Properties-SmallStep-NO₂
import 4-3-Properties-SmallStep-CBV
import 4-4-Properties-SmallStep-AO
import 4-5-Properties-SmallStep-HAO
import 4-6-Properties-SmallStep-HS
import 4-7-1-Properties-SmallStep-H
import 4-7-2-Properties-SmallStep-H₂
import 4-8-1-Properties-SmallStep-HNO
import 4-8-2-Properties-SmallStep-HNO₂

open import 5-1-Equivalence-CBN
open import 5-2-Equivalence-NO
open import 5-3-Equivalence-CBV
open import 5-4-Equivalence-AO
open import 5-5-Equivalence-HAO
open import 5-6-Equivalence-HS
open import 5-7-Equivalence-H
open import 5-8-Equivalence-HNO


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to weak head normal forms

-- Theorem 5.1.3.  SS-CBN to WHNF and BS-CBN coincide

thm-5-1-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBN.⇒* e′ × WHNF e′) ↔ e BS.CBN.⟱ e′
thm-5-1-3 = Thm-5-1-3.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Normal order reduction to normal forms

-- Theorem 5.2.6.  SS-NO to NF and BS-NO coincide

thm-5-2-6 : ∀ {n} {e : Tm n} {e′} → (e SS.NO.⇒* e′ × NF e′) ↔ e BS.NO.⟱ e′
thm-5-2-6 = Thm-5-2-6.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to weak normal forms

-- Theorem 5.3.3.  SS-CBV to WNF and BS-CBV coincide

thm-5-3-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBV.⇒* e′ × WNF e′) ↔ e BS.CBV.⟱ e′
thm-5-3-3 = Thm-5-3-3.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Applicative order reduction to normal forms

-- Theorem 5.4.3.  SS-AO to NF and BS-AO coincide

thm-5-4-3 : ∀ {n} {e : Tm n} {e′} → (e SS.AO.⇒* e′ × NF e′) ↔ e BS.AO.⟱ e′
thm-5-4-3 = Thm-5-4-3.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid applicative order reduction to normal forms

-- Theorem 5.5.3.  SS-HAO to NF and BS-HAO coincide

thm-5-5-3 : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⟱ e′
thm-5-5-3 = Thm-5-5-3.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Head spine reduction to head normal forms

-- Theorem 5.6.3.  SS-HS to HNF and BS-HS coincide

thm-5-6-3 : ∀ {n} {e : Tm n} {e′} → (e SS.HS.⇒* e′ × HNF e′) ↔ e BS.HS.⟱ e′
thm-5-6-3 = Thm-5-6-3.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Head reduction to head normal forms

-- Theorem 5.7.6.  SS-H to HNF and BS-H coincide

thm-5-7-6 : ∀ {n} {e : Tm n} {e′} → (e SS.H.⇒* e′ × HNF e′) ↔ e BS.H.⟱ e′
thm-5-7-6 = Thm-5-7-6.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid normal order reduction to normal forms

-- Theorem 5.8.6.  SS-HNO to NF and BS-HNO coincide

thm-5-8-6 : ∀ {n} {e : Tm n} {e′} → (e SS.HNO.⇒* e′ × NF e′) ↔ e BS.HNO.⟱ e′
thm-5-8-6 = Thm-5-8-6.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- References
--
-- * A. Garcia-Perez, et al. (2013)
--   “Deriving the full-reducing Krivine machine from the small-step operational semantics of normal order”
--   http://oa.upm.es/30153/1/30153nogueiraINVES_MEM_2013.pdf
--
-- * J.C. Mitchell (1996)
--   “Foundations for programming languages”
--
-- * L. Paulson (1996)
--   “ML for the working programmer”
--   https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter9.pdf
--
-- * B. Pierce (2001)
--   “Types and programming languages”
--
-- * P. Sestoft (2002)
--   “Demonstrating lambda calculus reduction”
--   http://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf
--
-- * G. Winskel (1993)
--   “The formal semantics of programming languages”


---------------------------------------------------------------------------------------------------------------
