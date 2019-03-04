---------------------------------------------------------------------------------------------------------------
--
-- A formalisation of big-step and small-step operational semantics for λ-calculus

module Everything where

open import Prelude
open import Syntax-Terms
open import Syntax-Predicates
import Semantics-SmallStep
import Semantics-SmallStep-CBN as SS-CBN
import Semantics-SmallStep-NO₊ as SS-NO₊
import Semantics-SmallStep-NO as SS-NO
import Semantics-SmallStep-CBV as SS-CBV
import Semantics-SmallStep-CBV₀ as SS-CBV₀
import Semantics-SmallStep-AO as SS-AO
import Semantics-SmallStep-HAO as SS-HAO
import Semantics-SmallStep-HS as SS-HS
import Semantics-SmallStep-H as SS-H
import Semantics-SmallStep-HNO as SS-HNO
import Semantics-BigStep
import Semantics-BigStep-CBN as BS-CBN
import Semantics-BigStep-CBN₀ as BS-CBN₀
import Semantics-BigStep-NO₊ as BS-NO₊
import Semantics-BigStep-NO as BS-NO
import Semantics-BigStep-CBV as BS-CBV
import Semantics-BigStep-CBV₀ as BS-CBV₀
import Semantics-BigStep-AO as BS-AO
import Semantics-BigStep-HAO as BS-HAO
import Semantics-BigStep-HS as BS-HS
import Semantics-BigStep-H as BS-H
import Semantics-BigStep-HNO as BS-HNO


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to weak head normal form

module CBN where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → WHNF e′ → e SS-CBN.⇒* e′ ↔ e BS-CBN.⇓ e′
  ss↔bs = BS-CBN.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to value

module CBN₀ where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → V e′ → e SS-CBN.⇒* e′ ↔ e BS-CBN₀.⇓ e′
  ss↔bs = BS-CBN₀.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Normal order reduction to normal form

module NO where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-NO.⇒* e′ ↔ e BS-NO.⇓ e′
  ss↔bs = BS-NO.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to weak normal form

module CBV where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → WNF e′ → e SS-CBV.⇒* e′ ↔ e BS-CBV.⇓ e′
  ss↔bs = BS-CBV.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to value

module CBV₀ where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → V e′ → e SS-CBV₀.⇒* e′ ↔ e BS-CBV₀.⇓ e′
  ss↔bs = BS-CBV₀.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Applicative order reduction to normal form

module AO where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-AO.⇒* e′ ↔ e BS-AO.⇓ e′
  ss↔bs = BS-AO.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Hybrid applicative order reduction to normal form

module HAO where
--   ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-HAO.⇒* e′ ↔ e BS-HAO.⇓ e′
--   ss↔bs = BS-HAO.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Head spine reduction to head normal form

module HS where
--   ss↔bs : ∀ {n} {e : Tm n} {e′} → HNF e′ → e SS-HS.⇒* e′ ↔ e BS-HS.⇓ e′
--   ss↔bs = BS-HS.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Head reduction to head normal form

module H where
--   ss↔bs : ∀ {n} {e : Tm n} {e′} → HNF e′ → e SS-H.⇒* e′ ↔ e BS-H.⇓ e′
--   ss↔bs = BS-H.ss↔bs


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Hybrid normal order reduction to normal form

module HNO where
--   ss↔bs : ∀ {n} {e : Tm n} {e′} → NF e′ → e SS-HNO.⇒* e′ ↔ e BS-HNO.⇓ e′
--   ss↔bs = BS-HNO.ss↔bs


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
