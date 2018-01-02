

renamings on terms

_∋⋆_       -- _≥_
putᵣ       -- (not needed)
getᵣ       -- renFin
wkᵣ        -- drop
liftᵣ      -- keep
idᵣ        -- id≥
ren        -- REN, MREN
wk         -- WK, MWK
_○_        -- _∘≥_

natgetᵣ    -- (not needed)
idgetᵣ     -- idrenFin
idren      -- idREN, idMREN

zap○       -- (not clear)
lid○       -- lid∘≥
rid○       -- rid∘≥

get○       -- assocrenFin
wk○        -- (not needed)
lift○      -- (not needed)
wklid○     -- ...
wkrid○     -- ...
liftwkrid○ -- ...
ren○       -- assocREN, assocMREN
renlift○   -- (easy from assocREN)
renwk○     -- ...
renliftwk○ -- ...

assoc○     -- assoc∘≥

(not here) -- commRENMREN




substitutions on terms

_⊢⋆_      -- Terms
putₛ       -- (not needed)
getₛ       -- get
wkₛ        -- WKS
liftₛ      -- LIFTS
idₛ        -- IDS
sub        -- SUB
cut        -- CUT
_●_        -- SUBS

natgetₛ    -- getWKS
idgetₛ     -- getIDS
idsub      -- idSUB

⌊_⌋        -- HYPS, MHYPS₁
_◐_        -- gets
_◑_        -- RENS, MRENS
⌊get⌋      -- ...
⌊wk⌋       -- ...
⌊lift⌋     -- ...
⌊id⌋       -- ...
⌊sub⌋      -- ...
⌊○⌋        -- ...

zap◐
rid◐

get◐
wk◐
lift◐
wkrid◐
litwkrid◐
sub◐
sublift◐
subwk◐
subliftwk◐ --

zap◑
lid◑       -- idRENS

zap●
lid●
rid●

get◑
wk◑
lift◑
wklid◑
liftwklid◑
sub◑
sublift◑
subwk◑
subliftwk◑

get●
wk●
lift●
wklid●
wkrid●
liftwkrid●
sub●
sublift●
subwk●
subliftwk●

comp◐○
comp◑○
comp◑◐
comp◑●
comp●◐
comp●◑

assoc●
