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
REN e (VAR i)      = VAR (renF e i)
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
MREN e (MVAR i)     = MVAR (renF e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)


MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id≥) M


MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero


--------------------------------------------------------------------------------


Terms : Nat → Nat → Nat → Set
Terms d g x = Vec (Term d g) x


--------------------------------------------------------------------------------


RENS : ∀ {d g g′ x} → g′ ≥ g → Terms d g x
                    → Terms d g′ x
RENS e ζ = map (REN e) ζ


WKS : ∀ {d g x} → Terms d g x
                → Terms d (suc g) x
WKS ζ = RENS (drop id≥) ζ


LIFTS : ∀ {d g x} → Terms d g x
                  → Terms d (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ


IDS : ∀ {g d} → Terms d g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


--------------------------------------------------------------------------------


MRENS : ∀ {d d′ g x} → d′ ≥ d → Terms d g x
                     → Terms d′ g x
MRENS e ζ = map (MREN e) ζ


MWKS : ∀ {d g x} → Terms d g x
                 → Terms (suc d) g x
MWKS ζ = MRENS (drop id≥) ζ


--------------------------------------------------------------------------------


SUB : ∀ {d g x} → Terms d g x → Term d x
                → Term d g
SUB ζ (VAR i)      = get ζ i
SUB ζ (LAM M)      = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N)    = APP (SUB ζ M) (SUB ζ N)
SUB ζ (MVAR i)     = MVAR i
SUB ζ (BOX M)      = BOX M
SUB ζ (LETBOX M N) = LETBOX (SUB ζ M) (SUB (MWKS ζ) N)


CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------


Term₁ : Nat → Set
Term₁ d = Term d zero

Terms₁ : Nat → Nat → Set
Terms₁ d x = Vec (Term₁ d) x


--------------------------------------------------------------------------------


MRENS₁ : ∀ {d d′ x} → d′ ≥ d → Terms₁ d x
                    → Terms₁ d′ x
MRENS₁ e ζ = map (MREN e) ζ


MWKS₁ : ∀ {d x} → Terms₁ d x
                → Terms₁ (suc d) x
MWKS₁ ζ = MRENS₁ (drop id≥) ζ


MLIFTS₁ : ∀ {d x} → Terms₁ d x
                  → Terms₁ (suc d) (suc x)
MLIFTS₁ ζ = MWKS₁ ζ , MVZ


MIDS₁ : ∀ {d} → Terms₁ d d
MIDS₁ {zero}  = ∙
MIDS₁ {suc d} = MLIFTS₁ MIDS₁


--------------------------------------------------------------------------------


MSUB : ∀ {d g x} → Terms₁ d x → Term x g
                 → Term d g
MSUB ζ (VAR i)      = VAR i
MSUB ζ (LAM M)      = LAM (MSUB ζ M)
MSUB ζ (APP M N)    = APP (MSUB ζ M) (MSUB ζ N)
MSUB ζ (MVAR i)     = SUB ∙ (get ζ i)
MSUB ζ (BOX M)      = BOX (MSUB ζ M)
MSUB ζ (LETBOX M N) = LETBOX (MSUB ζ M) (MSUB (MLIFTS₁ ζ) N)


MCUT : ∀ {d g} → Term₁ d → Term (suc d) g
               → Term d g
MCUT M N = MSUB (MIDS₁ , M) N


--------------------------------------------------------------------------------


UNLAM : ∀ {d g} → Term d g
                → Term d (suc g)
UNLAM M = APP (WK M) VZ


EX : ∀ {d g} → Term d (suc (suc g))
             → Term d (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------


SHL : ∀ {d g} → Term d (suc g)
              → Term (suc d) g
SHL M = APP (LAM (MWK M)) (BOX MVZ)


SHR : ∀ {d g} → Term (suc d) g
              → Term d (suc g)
SHR M = LETBOX VZ (WK M)


MEX : ∀ {d g} → Term (suc (suc d)) g
              → Term (suc (suc d)) g
MEX M = SHL (SHL (EX (SHR (SHR M))))


--------------------------------------------------------------------------------
