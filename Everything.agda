module Everything where


--------------------------------------------------------------------------------


import Prelude

import Names

import Category

import Fin
import FinLemmas

import List
import ListLemmas

import ListConcatenation

import AllList
import AllListLemmas

import Vec
import VecLemmas

import AllVec
import AllVecLemmas


--------------------------------------------------------------------------------


import IPLPropositions

import IPLDerivations               -- _⊢_true ; var/lam/app
import IPLExperimentalDerivations1  -- _⊢_true ; vz/wk/lam/app
import IPLExperimentalDerivations2  -- _⊢_true ; vz/wk/cut/lam/unlam ; preferred
import IPLExperimentalDerivations3  -- _⊢_true ; var/cut/lam/unlam   ; problematic

import IPLLemmas

import IPLBidirectionalDerivationsForNormalisation
import IPLNormalisation


--------------------------------------------------------------------------------


import STLCTypes

import STLCTerms
import STLCDerivations          -- ⊢_⦂_valid[_] ; var/lam/app
import STLCStandardDerivations  -- _⊢_⦂_true    ; var/lam/app

import STLCIsomorphismWithIPL

import STLCBidirectionalTermsForTypeChecking
import STLCBidirectionalDerivationsForTypeChecking
import STLCTypeChecking

import STLCNameResolution


--------------------------------------------------------------------------------


import S4Propositions

import S4Derivations               -- _⊢_valid[_] ; var/lam/app         ; mvar/box/letbox
import S4ExperimentalDerivations1  -- _⊢_valid[_] ; vz/wk/lam/app       ; mvz/mwk/box/letbox
import S4ExperimentalDerivations2  -- _⊢_valid[_] ; vz/wk/cut/lam/unlam ; mvz/mwk/box/letbox
import S4ExperimentalDerivations3  -- _⊢_valid[_] ; vz/wk/cut/lam/unlam ; mvz/mwk/mcut/vau/unvau
import S4ExperimentalDerivations4  -- _⊢_valid[_] ; vz/wk/cut/lam/unlam ; box/unbox/vau/unvau    ; preferred
import S4ExperimentalDerivations5  -- _⊢_valid[_] ; vz/wk/cut/lam/unlam ; mvz/mwk/mcut/box/unbox ; problematic
import S4StandardDerivations       -- _⨾_⊢_true   ; var/lam/app         ; mvar/box/letbox

import S4Lemmas

import S4ProjectionToIPL

import S4BidirectionalDerivationsForNormalisation
import S4Normalisation


--------------------------------------------------------------------------------


import S4TTTypes

import S4TTTerms
import S4TTDerivations          -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import S4TTStandardDerivations  -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

import S4TTIsomorphismWithS4

import S4TTTermsLemmas


--------------------------------------------------------------------------------


import CMLPropositions

import CMLDerivations              -- _⊢_valid[_] ; var/lam/app         ; mvar/box/unbox
import CMLExperimentalDerivations  -- _⊢_valid[_] ; vz/wk/cut/lam/unlam ; box/unbox/vau/unvau
import CMLStandardDerivations      -- _⨾_⊢_true   ; var/lam/app         ; mvar/box/unbox

import CMLLemmas

import CMLProjectionToIPL

import CMLBidirectionalDerivationsForNormalisation
import CMLNormalisation


--------------------------------------------------------------------------------


import CMTTTypes

import CMTTTerms
import CMTTDerivations          -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import CMTTStandardDerivations  -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

-- import CMTTIsomorphismWithCML


--------------------------------------------------------------------------------


import LPTTTypes
import LPTTTypesLemmas

import LPTTAsserts

import LPTTDerivations

-- import StdLPTT
-- import StdLPTTLemmas


--------------------------------------------------------------------------------
