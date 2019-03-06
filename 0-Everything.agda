---------------------------------------------------------------------------------------------------------------
--
-- A formalisation of big-step and small-step operational semantics for λ-calculus

module 0-Everything where

open import 1-0-Prelude

open import 1-1-Syntax-Terms
open import 1-2-Syntax-Predicates

import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS

import 2-1-Properties-SmallStep-CBN
import 2-2-1-Properties-SmallStep-NO
import 2-2-2-Properties-SmallStep-NO₂
import 2-3-Properties-SmallStep-CBV
import 2-4-Properties-SmallStep-AO
import 2-5-1-Properties-SmallStep-HAO
-- import 2-5-2-Properties-SmallStep-HAO₂
import 2-6-Properties-SmallStep-HS
import 2-7-1-Properties-SmallStep-H
-- import 2-7-2-Properties-SmallStep-H₂
import 2-8-1-Properties-SmallStep-HNO
-- import 2-8-2-Properties-SmallStep-HNO₂

import 3-1-Properties-BigStep-CBN
import 3-2-1-Properties-BigStep-NO
import 3-2-2-Properties-BigStep-NO₂
import 3-3-Properties-BigStep-CBV
import 3-4-Properties-BigStep-AO
import 3-5-1-Properties-BigStep-HAO
-- import 3-5-2-Properties-BigStep-HAO₂
import 3-6-Properties-BigStep-HS
import 3-7-1-Properties-BigStep-H
-- import 3-7-2-Properties-BigStep-H
import 3-8-1-Properties-BigStep-HNO
-- import 3-8-2-Properties-BigStep-HNO

import 4-1-Equivalence-CBN as CBN
import 4-2-Equivalence-NO  as NO
import 4-3-Equivalence-CBV as CBV
import 4-4-Equivalence-AO  as AO
import 4-5-Equivalence-HAO as HAO
import 4-6-Equivalence-HS  as HS
import 4-7-Equivalence-H   as H
import 4-8-Equivalence-HNO as HNO


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to weak head normal forms

-- Theorem 4.1.3.  SS-CBN to WHNF and BS-CBN coincide

thm-4-1-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBN.⇒* e′ × WHNF e′) ↔ e BS.CBN.⇓ e′
thm-4-1-3 = CBN.Thm-4-1-3.ss-cbn↔bs-cbn


---------------------------------------------------------------------------------------------------------------
--
-- Normal order reduction to normal forms

-- Theorem 4.2.6.  SS-NO to NF and BS-NO coincide

thm-4-2-6 : ∀ {n} {e : Tm n} {e′} → (e SS.NO.⇒* e′ × NF e′) ↔ e BS.NO.⇓ e′
thm-4-2-6 = NO.Thm-4-2-6.ss-no↔bs-no


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to weak normal forms

-- Theorem 4.3.3.  SS-CBV to WNF and BS-CBV coincide

thm-4-3-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBV.⇒* e′ × WNF e′) ↔ e BS.CBV.⇓ e′
thm-4-3-3 = CBV.Thm-4-3-3.ss-cbv↔bs-cbv


---------------------------------------------------------------------------------------------------------------
--
-- Applicative order reduction to normal forms

-- Theorem 4.4.3.  SS-AO to NF and BS-AO coincide

thm-4-4-3 : ∀ {n} {e : Tm n} {e′} → (e SS.AO.⇒* e′ × NF e′) ↔ e BS.AO.⇓ e′
thm-4-4-3 = AO.Thm-4-4-3.ss-ao↔bs-ao


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid applicative order reduction to normal forms

-- Theorem 4.5.6.  SS-HAO to NF and BS-HAO coincide

-- thm-4-5-6 : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
-- thm-4-5-6 = HAO.Thm-4-5-6.ss-hao↔bs-hao


---------------------------------------------------------------------------------------------------------------
--
-- Head spine reduction to head normal forms

-- Theorem 4.6.3.  SS-HS to HNF and BS-HS coincide

thm-4-6-3 : ∀ {n} {e : Tm n} {e′} → (e SS.HS.⇒* e′ × HNF e′) ↔ e BS.HS.⇓ e′
thm-4-6-3 = HS.Thm-4-6-3.ss-hs↔bs-hs


---------------------------------------------------------------------------------------------------------------
--
-- Head reduction to head normal forms

-- Theorem 4.7.6.  SS-H to HNF and BS-H coincide

-- thm-4-7-6 : ∀ {n} {e : Tm n} {e′} → (e SS.H.⇒* e′ × HNF e′) ↔ e BS.H.⇓ e′
-- thm-4-7-6 = H.Thm-4-7-6.ss-h↔bs-h


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid normal order reduction to normal forms

-- Theorem 4.8.6.  SS-HNO to NF and BS-HNO coincide

-- thm-4-8-6 : ∀ {n} {e : Tm n} {e′} → (e SS.HNO.⇒* e′ × NF e′) ↔ e BS.HNO.⇓ e′
-- thm-4-8-6 = HNO.Thm-4-8-6.ss-hno↔bs-hno


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
