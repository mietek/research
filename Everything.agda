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

import IPLDerivations               -- _⊢_ ; var/lam/app
import IPLExperimentalDerivations1  -- _⊢_ ; vz/wk/lam/app
import IPLExperimentalDerivations2  -- _⊢_ ; vz/wk/cut/lam/unlam
import IPLExperimentalDerivations3  -- _⊢_ ; var/cut/lam/unlam ; problem with renaming

import IPLLemmas

import IPLBidirectionalDerivationsForNormalisation
import IPLNormalisation


--------------------------------------------------------------------------------


import STLCTypes

import STLCTerms
import STLCDerivations          -- ⊢_⦂_valid[_] ; var/lam/app
import STLCStandardDerivations  -- _⊢_⦂_        ; var/lam/app

-- TODO: Below

import STLCBidirectionalTermsForTypeChecking
import STLCBidirectionalDerivationsForTypeChecking
import STLCTypeChecking

import STLCBidirectionalTermsForNameResolution
import STLCBidirectionalDerivationsForNameResolution
import STLCNameResolution


--------------------------------------------------------------------------------


import S4Propositions

import S4Derivations                   -- _⊢_valid[_] ; var/lam/app ; mvar/box/letbox
import S4StandardDerivations           -- _⨾_⊢_       ; var/lam/app ; mvar/box/letbox
import S4ExperimentalDerivations1      -- vz/wk/lam/app; mvz/mwk/box/letbox
-- import S4ExperimentalDerivations2      -- vz/wk/cut/lam/unlam; mvz/mwk/box/letbox
-- import S4ExperimentalDerivations3      -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/vau/unvau
-- import S4ExperimentalDerivations3x     -- 3 + explicit conversions
-- import S4ExperimentalDerivations4      -- vz/wk/cut/lam/unlam; box/unbox/vau/unvau
-- -- import S4ExperimentalDerivations5   -- vz/wk/cut/lam/unlam; mvz/mwk/mcut/box/unbox; problem with vau

-- import S4Lemmas

-- import S4BidirectionalDerivationsForNormalisation
-- import S4Normalisation


-- -- import RealS4Derivations

-- -- import S4ExperimentalDerivations0a                                      
-- -- import S4ExperimentalDerivations1a                                      
-- -- import S4ExperimentalDerivations3a                                      
-- -- import S4ExperimentalDerivations3x                                      
-- -- import S4ExperimentalDerivations4a

-- -- import StdS4                                                            
-- -- import StdS4Lemmas                                                      
-- -- import StdS4NormalForms                                                 
-- -- import StdS4Semantics

-- -- import Alt1-S4                                                          
-- -- import Alt1-S4NormalForms                                               
-- -- import Alt1-S4Semantics                                                 
-- -- import Alt2-S4                                 

-- -- import SymS4


-- --------------------------------------------------------------------------------


-- -- import StdS4TT                                                          
-- -- import StdS4TTTerms                                                     
-- -- import StdS4TTTermsLemmas


-- --------------------------------------------------------------------------------


-- import CMLPropositions

-- import CMLDerivations

-- import CMLLemmas


-- -- import StdCML                                                           
-- -- import StdCMLNormalForms                                                
-- -- import StdCMLSemantics


-- --------------------------------------------------------------------------------


-- -- import StdCMTT                                                          
-- -- import StdCMTTTerms


-- --------------------------------------------------------------------------------


-- -- import StdLPTT                                                          
-- -- import StdLPTTLemmas


-- --------------------------------------------------------------------------------
