module A201801.STLCStandardTerms where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec


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
RENS e τ = MAPS (REN e) τ


--------------------------------------------------------------------------------


WK : ∀ {g} → Term g
           → Term (suc g)
WK M = REN (drop id) M


WKS : ∀ {g n} → Terms g n
              → Terms (suc g) n
WKS τ = RENS (drop id) τ


VZ : ∀ {g} → Term (suc g)
VZ = VAR zero


LIFTS : ∀ {g n} → Terms g n
                → Terms (suc g) (suc n)
LIFTS τ = WKS τ , VZ


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
SUB τ (VAR I)    = GET τ I
SUB τ (LAM M)    = LAM (SUB (LIFTS τ) M)
SUB τ (APP M N)  = APP (SUB τ M) (SUB τ N)


SUBS : ∀ {g n m} → Terms g n → Terms n m
                 → Terms g m
SUBS τ υ = MAPS (SUB τ) υ


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
PSEUDOSUB (τ , L) M = APP (PSEUDOSUB τ (LAM M)) L


EXCH : ∀ {g} → Term (suc (suc g))
             → Term (suc (suc g))
EXCH M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------
