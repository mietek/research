module Everything where


--------------------------------------------------------------------------------


import Prelude

import Category

import Fin
import FinLemmas

import List
import ListLemmas

import AllList
import AllListLemmas

import Vec
import VecLemmas

import AllVec
import AllVecLemmas


--------------------------------------------------------------------------------


import IPLPropositions

import SimpleIPLDerivations  -- var/lam/app
import SimpleIPLLemmas
import SimpleIPLVerifications
import SimpleIPLSemantics

import ExperimentalIPLDerivations1  -- vz/wk/lam/app
import ExperimentalIPLDerivations2  -- vz/wk/cut/lam/unlam


--------------------------------------------------------------------------------


import S4Propositions

import SimpleS4Derivations  -- var/lam/app; mvar/box/letbox
import SimpleS4Lemmas
import SimpleS4Verifications
import SimpleS4Semantics

import ExperimentalS4Derivations1  -- vz/wk/lam/app;       mvz/mwk/box/letbox
import ExperimentalS4Derivations2  -- vz/wk/cut/lam/unlam; mvz/mwk/box/letbox
import ExperimentalS4Derivations3  -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/vau/unvau
import ExperimentalS4Derivations4  -- vz/wk/cut/lam/unlam; box/unbox/vau/unvau
-- import ExperimentalS4Derivations5  -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/box/unbox; missing letbox

import ExperimentalS4Derivations0a  -- Simple + contextual validity
import ExperimentalS4Derivations2a  -- 2 + contextual validity
import ExperimentalS4Derivations3a  -- 3 + contextual validity
import ExperimentalS4Derivations4a  -- 4 + contextual validity

import ExperimentalS4Derivations3x  -- 3 + explicit conversions

--------------------------------------------------------------------------------


-- import StdIPLLemmas
-- import StdIPLNormalForms
-- import StdIPLSemantics

-- import StdS4
-- import StdS4Lemmas
-- import StdS4NormalForms
-- import StdS4Semantics

-- import StdCML
-- import StdCMLNormalForms
-- import StdCMLSemantics

-- import StdSTLCTerms
-- import StdSTLC

-- import StdS4TTTerms
-- import StdS4TTTermsLemmas
-- import StdS4TT

-- import StdCMTTTerms
-- import StdCMTT

-- import StdLPTT
-- -- import StdLPTTLemmas


-- --------------------------------------------------------------------------------


-- import SymIPL


-- --------------------------------------------------------------------------------


-- import Alt1-S4
-- import Alt1-S4NormalForms
-- -- import Alt1-S4Semantics


-- --------------------------------------------------------------------------------
