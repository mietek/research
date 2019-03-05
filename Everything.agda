---------------------------------------------------------------------------------------------------------------
--
-- A formalisation of big-step and small-step operational semantics for λ-calculus

module Everything where

open import Prelude

open import Syntax-Terms
open import Syntax-Predicates

import Semantics-SmallStep
import Semantics-SmallStep-CBN  as SS-CBN
import Semantics-SmallStep-NO₊  as SS-NO₊
import Semantics-SmallStep-NO   as SS-NO
import Semantics-SmallStep-NO′  as SS-NO′
import Semantics-SmallStep-CBV  as SS-CBV
import Semantics-SmallStep-CBV₀ as SS-CBV₀
import Semantics-SmallStep-AO   as SS-AO
import Semantics-SmallStep-HAO  as SS-HAO
import Semantics-SmallStep-HS   as SS-HS
import Semantics-SmallStep-H    as SS-H
import Semantics-SmallStep-HNO  as SS-HNO

import Semantics-BigStep
import Semantics-BigStep-CBN  as BS-CBN
import Semantics-BigStep-CBN₀ as BS-CBN₀
import Semantics-BigStep-NO₊  as BS-NO₊
import Semantics-BigStep-NO   as BS-NO
import Semantics-BigStep-CBV  as BS-CBV
import Semantics-BigStep-CBV₀ as BS-CBV₀
import Semantics-BigStep-AO   as BS-AO
import Semantics-BigStep-HAO  as BS-HAO
import Semantics-BigStep-HS   as BS-HS
import Semantics-BigStep-H    as BS-H
import Semantics-BigStep-HNO  as BS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to weak head normal forms

module CBN where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-CBN.⇓ e′ ↔ (e SS-CBN.⇒* e′ × WHNF e′)
  bs↔ss = BS-CBN.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to values

module CBN₀ where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-CBN₀.⇓ e′ ↔ (e SS-CBN.⇒* e′ × V e′)
  bs↔ss = BS-CBN₀.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Normal order reduction to normal forms

module NO where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-NO.⇓ e′ ↔ (e SS-NO.⇒* e′ × NF e′)
  bs↔ss = BS-NO.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to weak normal forms

module CBV where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-CBV.⇓ e′ ↔ (e SS-CBV.⇒* e′ × WNF e′)
  bs↔ss = BS-CBV.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to values

module CBV₀ where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-CBV₀.⇓ e′ ↔ (e SS-CBV₀.⇒* e′ × V e′)
  bs↔ss = BS-CBV₀.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Applicative order reduction to normal forms

module AO where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-AO.⇓ e′ ↔ (e SS-AO.⇒* e′ × NF e′)
  bs↔ss = BS-AO.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Hybrid applicative order reduction to normal forms

module HAO where
--   bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-HAO.⇓ e′ ↔ (e SS-HAO.⇒* e′ × NF e′)
--   bs↔ss = BS-HAO.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- Head spine reduction to head normal forms

module HS where
  bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-HS.⇓ e′ ↔ (e SS-HS.⇒* e′ × HNF e′)
  bs↔ss = BS-HS.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Head reduction to head normal forms

module H where
--   bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-H.⇓ e′ ↔ (e SS-H.⇒* e′ × HNF e′)
--   bs↔ss = BS-H.bs↔ss


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Hybrid normal order reduction to normal forms

module HNO where
--   bs↔ss : ∀ {n} {e : Tm n} {e′} → e BS-HNO.⇓ e′ ↔ (e SS-HNO.⇒* e′ × NF e′)
--   bs↔ss = BS-HNO.bs↔ss


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
