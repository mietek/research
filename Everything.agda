module Everything where


--------------------------------------------------------------------------------


import Prelude

import Names

import Category
import Category2
import Subset

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

import IPLStandardDerivations                                                   -- _⊢_true ; var/lam/app
import IPLStandardDerivationsLemmas
import IPLStandardBidirectionalDerivations-NormalNeutral
import IPLStandardDerivationsWithAFriendlyFish
import IPLStandardNormalisation

import IPLExperimentalDerivations-Monolithic                                    -- _⊢_true ; vz/wk/lam/app
import IPLExperimentalDerivations-Symmetric                                     -- _⊢_true ; var/cut/lam/unlam ; problematic

import IPLAlternativeDerivations                                                -- _⊢_true ; vz/wk/cut/lam/unlam


import STLCTypes

import STLCStandardTerms
import STLCStandardDerivations                                                  -- ⊢_⦂_valid[_] ; var/lam/app
import STLCStandardDerivations-Traditional                                      -- _⊢_⦂_true    ; var/lam/app
import STLCStandardIsomorphismWithIPL
import STLCStandardBidirectionalTerms-CheckedInferred
import STLCStandardBidirectionalDerivations-CheckedInferred
import STLCStandardTypeChecking
import STLCStandardNameResolution


--------------------------------------------------------------------------------


import S4Propositions

import S4StandardDerivations                                                    -- _⊢_valid[_] ; var/lam/app/mvar/box/letbox
import S4StandardDerivations-Traditional                                        -- _⨾_⊢_true   ; var/lam/app/mvar/box/letbox
import S4StandardBidirectionalDerivations-NormalNeutral
import S4StandardDerivationsLemmas
import S4StandardNormalisation

import S4ExperimentalDerivations-Monolithic                                     -- _⊢_valid[_] ; vz/wk/lam/app/mvz/mwk/box/letbox
import S4ExperimentalDerivations-PartiallySymmetric                             -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/box/letbox
import S4ExperimentalDerivations-RedundantlySymmetric                           -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/mcut/vau/unvau
import S4ExperimentalDerivations-Incomplete                                     -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/mcut/box/unbox ; problematic

import S4AlternativeDerivations                                                 -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/box/unbox/vau/unvau


import S4EmbeddingOfIPL
import S4ProjectionToIPL


-- TODO: unfinished
import S4AndCMLScratch
import S4ExperimentalDerivations3x
import S4NewBidirectionalDerivationsForNormalisation
import S4NewNormalisation
import S4NewNormalisation2


-------------------


import S4TTTypes

import S4TTTerms
import S4TTDerivations          -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import S4TTStandardDerivations  -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

import S4TTIsomorphismWithS4

import S4TTTermsLemmas


--------------------------------------------------------------------------------


import CMLPropositions

import CMLStandardDerivations                                                   -- _⊢_valid[_] ; var/lam/app/mvar/box/unbox
import CMLStandardDerivations-Traditional                                       -- _⨾_⊢_true   ; var/lam/app/mvar/box/unbox
import CMLStandardDerivationsLemmas
import CMLStandardBidirectionalDerivations-NormalNeutral
import CMLStandardNormalisation

import CMLAlternativeDerivations                                                -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/box/unbox/vau/unvau

import CMLProjectionToIPL

-- TODO: unfinished
import CMLAndS4Scratch
import CMLEnlightenment
import CMLProjectionToS4


-------------------


import CMTTTypes

import CMTTTerms
import CMTTDerivations          -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import CMTTStandardDerivations  -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

-- TODO: unfinished
import CMTTIsomorphismWithCML
import StdCMTTTerms


--------------------------------------------------------------------------------


import LPTTTypes
import LPTTTypesLemmas

import LPTTAsserts

import LPTTDerivations

-- TODO: unfinished
import StdLPTT
import StdLPTTLemmas


--------------------------------------------------------------------------------


import FullIPLPropositions

import FullIPLDerivations

import FullIPLBidirectionalDerivationsForNormalisation
import FullIPLNormalisation


---------------------------------------


import FullS4Propositions

import FullS4StandardDerivations

import FullS4EmbeddingOfFullIPL
import FullS4ProjectionToFullIPL

import FullS4BidirectionalDerivationsForNormalisation

-- TODO: unfinished
import FullS4Normalisation


--------------------------------------------------------------------------------


-- TODO: unfinished
import Scratch
import SequentCalculusDraft
import SequentCalculusDrafta
import SequentCalculusDraftSquasha
import SequentCalculusDraft2a
import SequentCalculusDraft2b
import SequentCalculusDraft2c


--------------------------------------------------------------------------------
