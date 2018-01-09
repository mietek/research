module StdS4TTTerms where

open import Prelude
open import Fin
open import Vec


--------------------------------------------------------------------------------


data Term : Nat → Nat → Set
  where
    VAR    : ∀ {d g} → Fin g → Term d g
    LAM    : ∀ {d g} → Term d (suc g) → Term d g
    APP    : ∀ {d g} → Term d g → Term d g → Term d g
    MVAR   : ∀ {d g} → Fin d → Term d g
    BOX    : ∀ {d g} → Term d zero → Term d g
    LETBOX : ∀ {d g} → Term d g → Term (suc d) g → Term d g


--------------------------------------------------------------------------------


REN : ∀ {d g g′} → g′ ≥ g → Term d g
                 → Term d g′
REN e (VAR i)      = VAR (REN∋ e i)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (MVAR i)     = MVAR i
REN e (BOX M)      = BOX M
REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)


WK : ∀ {d g} → Term d g
             → Term d (suc g)
WK M = REN (drop id≥) M


VZ : ∀ {d g} → Term d (suc g)
VZ = VAR zero


--------------------------------------------------------------------------------


MREN : ∀ {d d′ g} → d′ ≥ d → Term d g
                  → Term d′ g
MREN e (VAR i)      = VAR i
MREN e (LAM M)      = LAM (MREN e M)
MREN e (APP M N)    = APP (MREN e M) (MREN e N)
MREN e (MVAR i)     = MVAR (REN∋ e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)


MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id≥) M


MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero


--------------------------------------------------------------------------------


Terms : Nat → Nat → Nat → Set
Terms d g n = Vec (Term d g) n


--------------------------------------------------------------------------------


RENS : ∀ {d g g′ n} → g′ ≥ g → Terms d g n
                    → Terms d g′ n
RENS e x = MAPS (REN e) x


WKS : ∀ {d g n} → Terms d g n
                → Terms d (suc g) n
WKS x = RENS (drop id≥) x


LIFTS : ∀ {d g n} → Terms d g n
                  → Terms d (suc g) (suc n)
LIFTS x = WKS x , VZ


VARS : ∀ {d g g′} → g′ ≥ g
                  → Terms d g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)


IDS : ∀ {d g} → Terms d g g
IDS = VARS id≥


--------------------------------------------------------------------------------


MRENS : ∀ {d d′ g n} → d′ ≥ d → Terms d g n
                     → Terms d′ g n
MRENS e x = MAPS (MREN e) x


MWKS : ∀ {d g n} → Terms d g n
                 → Terms (suc d) g n
MWKS x = MRENS (drop id≥) x


--------------------------------------------------------------------------------


SUB : ∀ {d g n} → Terms d g n → Term d n
                → Term d g
SUB x (VAR i)      = GET x i
SUB x (LAM M)      = LAM (SUB (LIFTS x) M)
SUB x (APP M N)    = APP (SUB x M) (SUB x N)
SUB x (MVAR i)     = MVAR i
SUB x (BOX M)      = BOX M
SUB x (LETBOX M N) = LETBOX (SUB x M) (SUB (MWKS x) N)


CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------


SUBS : ∀ {d g n m} → Terms d g n → Terms d n m
                   → Terms d g m
SUBS x y = MAPS (SUB x) y


--------------------------------------------------------------------------------


Term₁ : Nat → Set
Term₁ d = Term d zero


Terms₁ : Nat → Nat → Set
Terms₁ d n = Vec (Term₁ d) n


--------------------------------------------------------------------------------


MRENS₁ : ∀ {d d′ n} → d′ ≥ d → Terms₁ d n
                    → Terms₁ d′ n
MRENS₁ e x = MRENS e x


MWKS₁ : ∀ {d n} → Terms₁ d n
                → Terms₁ (suc d) n
MWKS₁ x = MWKS x


MLIFTS₁ : ∀ {d n} → Terms₁ d n
                  → Terms₁ (suc d) (suc n)
MLIFTS₁ x = MWKS₁ x , MVZ


MVARS₁ : ∀ {d d′} → d′ ≥ d
                  → Terms₁ d′ d
MVARS₁ done     = ∙
MVARS₁ (drop e) = MWKS₁ (MVARS₁ e)
MVARS₁ (keep e) = MLIFTS₁ (MVARS₁ e)


MIDS₁ : ∀ {d} → Terms₁ d d
MIDS₁ = MVARS₁ id≥


--------------------------------------------------------------------------------


MSUB : ∀ {d g n} → Terms₁ d n → Term n g
                 → Term d g
MSUB x (VAR i)      = VAR i
MSUB x (LAM M)      = LAM (MSUB x M)
MSUB x (APP M N)    = APP (MSUB x M) (MSUB x N)
MSUB x (MVAR i)     = SUB ∙ (GET x i)
MSUB x (BOX M)      = BOX (MSUB x M)
MSUB x (LETBOX M N) = LETBOX (MSUB x M) (MSUB (MLIFTS₁ x) N)


MCUT : ∀ {d g} → Term₁ d → Term (suc d) g
               → Term d g
MCUT M N = MSUB (MIDS₁ , M) N


--------------------------------------------------------------------------------


MSUBS : ∀ {d g n m} → Terms₁ d n → Terms n g m
                    → Terms d g m
MSUBS x y = MAPS (MSUB x) y


MSUBS₁ : ∀ {d n m} → Terms₁ d n → Terms₁ n m
                   → Terms₁ d m
MSUBS₁ x y = MSUBS x y


--------------------------------------------------------------------------------


UNLAM : ∀ {d g} → Term d g
                → Term d (suc g)
UNLAM M = APP (WK M) VZ


EX : ∀ {d g} → Term d (suc (suc g))
             → Term d (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------


UP : ∀ {d g} → Term d (suc g)
             → Term (suc d) g
UP M = APP (LAM (MWK M)) (BOX MVZ)


DOWN : ∀ {d g} → Term (suc d) g
               → Term d (suc g)
DOWN M = LETBOX VZ (WK M)


MEX : ∀ {d g} → Term (suc (suc d)) g
              → Term (suc (suc d)) g
MEX M = UP (UP (EX (DOWN (DOWN M))))


--------------------------------------------------------------------------------
