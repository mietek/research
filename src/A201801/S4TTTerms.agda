{-# OPTIONS --rewriting #-}

module A201801.S4TTTerms where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec


--------------------------------------------------------------------------------


data Term : Nat → Nat → Set
  where
    VAR    : ∀ {d g} → Fin g → Term d g
    LAM    : ∀ {d g} → Term d (suc g) → Term d g
    APP    : ∀ {d g} → Term d g → Term d g → Term d g
    MVAR   : ∀ {d g} → Fin d → Term d g
    BOX    : ∀ {d g} → Term d zero → Term d g
    LETBOX : ∀ {d g} → Term d g → Term (suc d) g → Term d g


Terms : Nat → Nat → Nat → Set
Terms d g n = Vec (Term d g) n


Terms* : Nat → Nat → Set
Terms* d n = Vec (Term d zero) n


--------------------------------------------------------------------------------


REN : ∀ {d g g′} → g′ ≥ g → Term d g
                 → Term d g′
REN e (VAR i)      = VAR (REN∋ e i)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (MVAR i)     = MVAR i
REN e (BOX M)      = BOX M
REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)


RENS : ∀ {d g g′ n} → g′ ≥ g → Terms d g n
                    → Terms d g′ n
RENS e τ = MAPS (REN e) τ


--------------------------------------------------------------------------------


MREN : ∀ {d d′ g} → d′ ≥ d → Term d g
                  → Term d′ g
MREN e (VAR i)      = VAR i
MREN e (LAM M)      = LAM (MREN e M)
MREN e (APP M N)    = APP (MREN e M) (MREN e N)
MREN e (MVAR i)     = MVAR (REN∋ e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)


MRENS : ∀ {d d′ g n} → d′ ≥ d → Terms d g n
                     → Terms d′ g n
MRENS e τ = MAPS (MREN e) τ


MRENS* : ∀ {d d′ n} → d′ ≥ d → Terms* d n
                    → Terms* d′ n
MRENS* e τ = MRENS e τ


--------------------------------------------------------------------------------


WK : ∀ {d g} → Term d g
             → Term d (suc g)
WK M = REN (drop id) M


WKS : ∀ {d g n} → Terms d g n
                → Terms d (suc g) n
WKS τ = RENS (drop id) τ


VZ : ∀ {d g} → Term d (suc g)
VZ = VAR zero


LIFTS : ∀ {d g n} → Terms d g n
                  → Terms d (suc g) (suc n)
LIFTS τ = WKS τ , VZ


VARS : ∀ {d g g′} → g′ ≥ g
                  → Terms d g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)


IDS : ∀ {d g} → Terms d g g
IDS = VARS id


--------------------------------------------------------------------------------


MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id) M


MWKS : ∀ {d g n} → Terms d g n
                 → Terms (suc d) g n
MWKS τ = MRENS (drop id) τ


MWKS* : ∀ {d n} → Terms* d n
                → Terms* (suc d) n
MWKS* τ = MWKS τ


MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero


MLIFTS* : ∀ {d n} → Terms* d n
                  → Terms* (suc d) (suc n)
MLIFTS* τ = MWKS* τ , MVZ


MVARS* : ∀ {d d′} → d′ ≥ d
                  → Terms* d′ d
MVARS* done     = ∙
MVARS* (drop e) = MWKS* (MVARS* e)
MVARS* (keep e) = MLIFTS* (MVARS* e)


MIDS* : ∀ {d} → Terms* d d
MIDS* = MVARS* id


--------------------------------------------------------------------------------


SUB : ∀ {d g n} → Terms d g n → Term d n
                → Term d g
SUB τ (VAR i)      = GET τ i
SUB τ (LAM M)      = LAM (SUB (LIFTS τ) M)
SUB τ (APP M N)    = APP (SUB τ M) (SUB τ N)
SUB τ (MVAR i)     = MVAR i
SUB τ (BOX M)      = BOX M
SUB τ (LETBOX M N) = LETBOX (SUB τ M) (SUB (MWKS τ) N)


SUBS : ∀ {d g n m} → Terms d g n → Terms d n m
                   → Terms d g m
SUBS τ υ = MAPS (SUB τ) υ


--------------------------------------------------------------------------------


MSUB : ∀ {d g n} → Terms* d n → Term n g
                 → Term d g
MSUB τ (VAR i)      = VAR i
MSUB τ (LAM M)      = LAM (MSUB τ M)
MSUB τ (APP M N)    = APP (MSUB τ M) (MSUB τ N)
MSUB τ (MVAR i)     = SUB ∙ (GET τ i)
MSUB τ (BOX M)      = BOX (MSUB τ M)
MSUB τ (LETBOX M N) = LETBOX (MSUB τ M) (MSUB (MLIFTS* τ) N)


MSUBS : ∀ {d g n m} → Terms* d n → Terms n g m
                    → Terms d g m
MSUBS τ υ = MAPS (MSUB τ) υ


MSUBS* : ∀ {d n m} → Terms* d n → Terms* n m
                   → Terms* d m
MSUBS* τ υ = MSUBS τ υ


--------------------------------------------------------------------------------


UNLAM : ∀ {d g} → Term d g
                → Term d (suc g)
UNLAM M = APP (WK M) VZ


CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


PSEUDOCUT : ∀ {d g} → Term d g → Term d (suc g)
                    → Term d g
PSEUDOCUT M N = APP (LAM N) M


PSEUDOSUB : ∀ {d g n} → Terms d g n → Term d n
                      → Term d g
PSEUDOSUB ∙       M = REN bot≥ M
PSEUDOSUB (τ , L) M = APP (PSEUDOSUB τ (LAM M)) L


EXCH : ∀ {d g} → Term d (suc (suc g))
               → Term d (suc (suc g))
EXCH M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------


VAU : ∀ {d g} → Term (suc d) g
              → Term d (suc g)
VAU M = LETBOX VZ (WK M)


UNVAU : ∀ {d g} → Term d (suc g)
                → Term (suc d) g
UNVAU M = APP (LAM (MWK M)) (BOX MVZ)


BOXAPP : ∀ {d g} → Term d g → Term d g
                 → Term d g
BOXAPP M N = LETBOX M (LETBOX (MWK N) (BOX (APP (MWK MVZ) MVZ)))


UNBOX : ∀ {d g} → Term d g
                → Term d g
UNBOX M = LETBOX M MVZ


REBOX : ∀ {d g} → Term d g
                → Term d g
REBOX M = LETBOX M (BOX MVZ)


DUPBOX : ∀ {d g} → Term d g
                 → Term d g
DUPBOX M = LETBOX M (BOX (BOX MVZ))


MCUT : ∀ {d g} → Term d zero → Term (suc d) g
               → Term d g
MCUT M N = MSUB (MIDS* , M) N


PSEUDOMCUT : ∀ {d g} → Term d zero → Term (suc d) g
                     → Term d g
PSEUDOMCUT M N = LETBOX (BOX M) N


PSEUDOMSUB : ∀ {d g n} → Terms* d n → Term n g
                       → Term d g
PSEUDOMSUB ∙       M = MREN bot≥ M
PSEUDOMSUB (τ , L) M = APP (PSEUDOMSUB τ (LAM (VAU M))) (BOX L)


MEXCH : ∀ {d g} → Term (suc (suc d)) g
                → Term (suc (suc d)) g
MEXCH M = UNVAU (UNVAU (EXCH (VAU (VAU M))))


--------------------------------------------------------------------------------
