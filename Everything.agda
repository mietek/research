module Everything where


--------------------------------------------------------------------------------


import Prelude

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

import IPLDerivations  -- var/lam/app
import IPLLemmas

import IPLBidirectionalDerivationsForNormalisation
import IPLNormalisation

import IPLExperimentalDerivations1  -- vz/wk/lam/app
import IPLExperimentalDerivations2  -- vz/wk/cut/lam/unlam
-- import IPLExperimentalDerivations3  -- var/cut/lam/unlam; problem with renaming


import STLCTypes

import STLCTerms
import STLCDerivations

import STLCBidirectionalTermsForTypeChecking
import STLCBidirectionalDerivationsForTypeChecking
import STLCTypeChecking

import STLCBidirectionalTermsForNameResolution
import STLCBidirectionalDerivationsForNameResolution
import STLCNameResolution


--------------------------------------------------------------------------------


import S4Propositions

import S4Derivations  -- var/lam/app; mvar/box/letbox
import S4Lemmas

import S4BidirectionalDerivationsForNormalisation
import S4Normalisation

import S4ExperimentalDerivations1  -- vz/wk/lam/app;       mvz/mwk/box/letbox
import S4ExperimentalDerivations2  -- vz/wk/cut/lam/unlam; mvz/mwk/box/letbox
import S4ExperimentalDerivations3  -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/vau/unvau
import S4ExperimentalDerivations3x -- + explicit conversions
import S4ExperimentalDerivations4  -- vz/wk/cut/lam/unlam; box/unbox/vau/unvau
-- import S4ExperimentalDerivations5  -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/box/unbox; problem with vau


-- import S4ExperimentalDerivations0a  -- contextual validity
-- import S4ExperimentalDerivations1a  -- 1 + contextual validity
-- import S4ExperimentalDerivations3a  -- 3 + contextual validity
-- import S4ExperimentalDerivations4a  -- 4 + contextual validity


--------------------------------------------------------------------------------



-- -- -- import StdIPLLemmas      -- done
-- -- -- import StdIPLNormalForms -- done
-- -- -- import StdIPLSemantics   -- done

-- -- -- import StdS4
-- -- -- import StdS4Lemmas
-- -- -- import StdS4NormalForms
-- -- -- import StdS4Semantics

-- -- -- import StdCML
-- -- -- import StdCMLNormalForms
-- -- -- import StdCMLSemantics

-- -- -- import StdSTLCTerms -- done
-- -- -- import StdSTLC      -- done

-- -- -- import StdS4TTTerms
-- -- -- import StdS4TTTermsLemmas
-- -- -- import StdS4TT

-- -- -- import StdCMTTTerms
-- -- -- import StdCMTT

-- -- -- import StdLPTT
-- -- -- -- import StdLPTTLemmas


-- -- -- --------------------------------------------------------------------------------


-- -- -- import SymIPL


-- -- -- --------------------------------------------------------------------------------


-- -- -- import Alt1-S4
-- -- -- import Alt1-S4NormalForms
-- -- -- -- import Alt1-S4Semantics


-- -- -- --------------------------------------------------------------------------------
