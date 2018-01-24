module STLCTerms where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import STLCTypes


--------------------------------------------------------------------------------


data Term : Nat → Set
  where
    VAR : ∀ {g} → Fin g → Term g
    LAM : ∀ {g} → Term (suc g) → Term g
    APP : ∀ {g} → Term g → Term g → Term g


Terms : Nat → Nat → Set
Terms g n = Vec (Term g) n


--------------------------------------------------------------------------------


REN : ∀ {g g′} → g′ ≥ g → Term g
               → Term g′
REN e (VAR I)    = VAR (REN∋ e I)
REN e (LAM M)    = LAM (REN (keep e) M)
REN e (APP M N)  = APP (REN e M) (REN e N)


RENS : ∀ {g g′ n} → g′ ≥ g → Terms g n
                  → Terms g′ n
RENS e x = MAPS (REN e) x


--------------------------------------------------------------------------------


WK : ∀ {g} → Term g
           → Term (suc g)
WK M = REN (drop id) M


VZ : ∀ {g} → Term (suc g)
VZ = VAR zero


WKS : ∀ {g n} → Terms g n
              → Terms (suc g) n
WKS x = RENS (drop id) x


LIFTS : ∀ {g n} → Terms g n
                → Terms (suc g) (suc n)
LIFTS x = WKS x , VZ


VARS : ∀ {g g′} → g′ ≥ g
                → Terms g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)


IDS : ∀ {g} → Terms g g
IDS = VARS id


--------------------------------------------------------------------------------


SUB : ∀ {g n} → Terms g n → Term n
              → Term g
SUB x (VAR I)    = GET x I
SUB x (LAM M)    = LAM (SUB (LIFTS x) M)
SUB x (APP M N)  = APP (SUB x M) (SUB x N)


SUBS : ∀ {g n m} → Terms g n → Terms n m
                 → Terms g m
SUBS x y = MAPS (SUB x) y


--------------------------------------------------------------------------------


UNLAM : ∀ {g} → Term g
              → Term (suc g)
UNLAM M = APP (WK M) VZ


CUT : ∀ {g} → Term g → Term (suc g)
            → Term g
CUT M N = SUB (IDS , M) N


PSEUDOCUT : ∀ {g} → Term g → Term (suc g)
                  → Term g
PSEUDOCUT M N = APP (LAM N) M


PSEUDOSUB : ∀ {g n} → Terms g n → Term n
                    → Term g
PSEUDOSUB ∙       M = REN bot≥ M
PSEUDOSUB (x , L) M = APP (PSEUDOSUB x (LAM M)) L


EXCH : ∀ {g} → Term (suc (suc g))
             → Term (suc (suc g))
EXCH M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------
