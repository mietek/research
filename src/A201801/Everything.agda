module A201801.Everything where


--------------------------------------------------------------------------------


import A201801.Prelude

import A201801.Names

import A201801.Category
import A201801.Category2 -- NOTE: unsafe!

import A201801.Fin
import A201801.FinLemmas

import A201801.List
import A201801.ListLemmas

import A201801.ListConcatenation

import A201801.AllList
import A201801.AllListLemmas

import A201801.Vec
import A201801.VecLemmas

import A201801.AllVec
import A201801.AllVecLemmas

import A201801.Subset -- TODO: check this!


--------------------------------------------------------------------------------


import A201801.IPLPropositions

import A201801.IPLStandardDerivations                                           -- _⊢_true ; var/lam/app
import A201801.IPLStandardDerivationsWithAFriendlyFish -- TODO: unfinished
import A201801.IPLStandardDerivationsLemmas
import A201801.IPLStandardBidirectionalDerivations-NormalNeutral
import A201801.IPLStandardNormalisation

import A201801.IPLExperimentalDerivations-Monolithic                            -- _⊢_true ; vz/wk/lam/app
import A201801.IPLExperimentalDerivations-Symmetric                             -- _⊢_true ; var/cut/lam/unlam ; problematic

import A201801.IPLAlternativeDerivations                                        -- _⊢_true ; vz/wk/cut/lam/unlam


import A201801.STLCTypes

import A201801.STLCStandardTerms
import A201801.STLCStandardDerivations                                          -- ⊢_⦂_valid[_] ; var/lam/app
import A201801.STLCStandardDerivations-Traditional                              -- _⊢_⦂_true    ; var/lam/app
import A201801.STLCStandardIsomorphismWithIPL
import A201801.STLCStandardBidirectionalTerms-CheckedInferred
import A201801.STLCStandardBidirectionalDerivations-CheckedInferred
import A201801.STLCStandardTypeChecking
import A201801.STLCStandardNameResolution


--------------------------------------------------------------------------------


import A201801.S4Propositions

import A201801.S4StandardDerivations                                            -- _⊢_valid[_] ; var/lam/app/mvar/box/letbox
import A201801.S4StandardDerivations-Traditional                                -- _⨾_⊢_true   ; var/lam/app/mvar/box/letbox
import A201801.S4StandardBidirectionalDerivations-NormalNeutral
import A201801.S4StandardDerivationsLemmas
import A201801.S4StandardNormalisation

import A201801.S4ExperimentalDerivations-Monolithic                             -- _⊢_valid[_] ; vz/wk/lam/app/mvz/mwk/box/letbox
import A201801.S4ExperimentalDerivations-PartiallySymmetric                     -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/box/letbox
import A201801.S4ExperimentalDerivations-RedundantlySymmetric                   -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/mcut/vau/unvau
import A201801.S4ExperimentalDerivations-Incomplete                             -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/mvz/mwk/mcut/box/unbox ; problematic

import A201801.S4AlternativeDerivations                                         -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/box/unbox/vau/unvau


import A201801.S4EmbeddingOfIPL
import A201801.S4ProjectionToIPL


import A201801.S4NewBidirectionalDerivationsForNormalisation
import A201801.S4NewNormalisation -- TODO: unfinished
import A201801.S4NewNormalisation2 -- TODO: unfinished

--

import A201801.S4AndCMLScratch -- TODO: check these!
import A201801.S4ExperimentalDerivations3x


-------------------


import A201801.S4TTTypes

import A201801.S4TTTerms
import A201801.S4TTDerivations                                                  -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import A201801.S4TTStandardDerivations                                          -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

import A201801.S4TTIsomorphismWithS4

import A201801.S4TTTermsLemmas


--------------------------------------------------------------------------------


import A201801.CMLPropositions

import A201801.CMLStandardDerivations                                           -- _⊢_valid[_] ; var/lam/app/mvar/box/unbox
import A201801.CMLStandardDerivations-Traditional                               -- _⨾_⊢_true   ; var/lam/app/mvar/box/unbox
import A201801.CMLStandardDerivationsLemmas
import A201801.CMLStandardBidirectionalDerivations-NormalNeutral
import A201801.CMLStandardNormalisation

import A201801.CMLAlternativeDerivations                                        -- _⊢_valid[_] ; vz/wk/cut/lam/unlam/box/unbox/vau/unvau

import A201801.CMLProjectionToIPL
import A201801.CMLProjectionToS4 -- TODO: unfinished

--

import A201801.CMLAndS4Scratch -- TODO: check these!
import A201801.CMLEnlightenment


-------------------


import A201801.CMTTTypes

import A201801.CMTTScopes
import A201801.CMTTTerms
import A201801.CMTTDerivations                                                  -- _⊢_⦂_valid[_] ; var/lam/app ; mvar/box/letbox
import A201801.CMTTStandardDerivations                                          -- _⨾_⊢_⦂_true   ; var/lam/app ; mvar/box/letbox

import A201801.CMTTIsomorphismWithCML -- TODO: unfinished

--

import A201801.StdCMTTTerms -- TODO: check these!


--------------------------------------------------------------------------------


import A201801.LPTTTypes
import A201801.LPTTTypesLemmas

import A201801.LPTTAsserts

import A201801.LPTTDerivations

import A201801.StdLPTT -- TODO: unfinished
import A201801.StdLPTTLemmas -- TODO: unfinished


--------------------------------------------------------------------------------


import A201801.FullIPLPropositions

import A201801.FullIPLDerivations

import A201801.FullIPLBidirectionalDerivationsForNormalisation
import A201801.FullIPLNormalisation


---------------------------------------


import A201801.FullS4Propositions

import A201801.FullS4StandardDerivations

import A201801.FullS4EmbeddingOfFullIPL
import A201801.FullS4ProjectionToFullIPL

import A201801.FullS4BidirectionalDerivationsForNormalisation
import A201801.FullS4Normalisation -- TODO: unfinished


--------------------------------------------------------------------------------

import A201801.Scratch -- TODO: check these!
import A201801.SequentCalculusDraft
import A201801.SequentCalculusDrafta
import A201801.SequentCalculusDraft2a
import A201801.SequentCalculusDraft2b
import A201801.SequentCalculusDraft2c
import A201801.SequentCalculusDraftSquasha -- TODO: unsafe!
