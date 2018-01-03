module StdSTLCTerms where

open import Prelude
open import Fin
open import Vec


--------------------------------------------------------------------------------


data Term : Nat → Set
  where
    VAR : ∀ {g} → Fin g → Term g
    LAM : ∀ {g} → Term (suc g) → Term g
    APP : ∀ {g} → Term g → Term g → Term g


--------------------------------------------------------------------------------


REN : ∀ {g g′} → g′ ≥ g → Term g
               → Term g′
REN e (VAR i)   = VAR (renF e i)
REN e (LAM M)   = LAM (REN (keep e) M)
REN e (APP M N) = APP (REN e M) (REN e N)


WK : ∀ {g} → Term g
           → Term (suc g)
WK M = REN (drop id≥) M


VZ : ∀ {g} → Term (suc g)
VZ = VAR zero


--------------------------------------------------------------------------------


Terms : Nat → Nat → Set
Terms g x = Vec (Term g) x


--------------------------------------------------------------------------------


RENS : ∀ {g g′ x} → g′ ≥ g → Terms g x
                  → Terms g′ x
RENS e ζ = map (REN e) ζ


WKS : ∀ {g x} → Terms g x
              → Terms (suc g) x
WKS ζ = RENS (drop id≥) ζ


LIFTS : ∀ {g x} → Terms g x
                → Terms (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ


IDS : ∀ {g} → Terms g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


--------------------------------------------------------------------------------


SUB : ∀ {g x} → Terms g x → Term x
              → Term g
SUB ζ (VAR i)   = get ζ i
SUB ζ (LAM M)   = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N) = APP (SUB ζ M) (SUB ζ N)


CUT : ∀ {g} → Term g → Term (suc g)
            → Term g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------


UNLAM : ∀ {g} → Term g
              → Term (suc g)
UNLAM M = APP (WK M) VZ


EX : ∀ {g} → Term (suc (suc g))
           → Term (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------
