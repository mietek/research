module LR0 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Type : Set
  where
    𝔹   : Type
    _∨_ : Type → Type → Type
    𝟘   : Type
    𝟙   : Type
    _∧_ : Type → Type → Type
    _⊃_ : Type → Type → Type


Types : Nat → Set
Types g = Vec Type g


--------------------------------------------------------------------------------


data Term (g : Nat) : Set
  where
    VAR   : Fin g → Term g
    LAM   : Term (suc g) → Term g
    APP   : Term g → Term g → Term g
    PAIR  : Term g → Term g → Term g
    FST   : Term g → Term g
    SND   : Term g → Term g
    UNIT  : Term g
    ABORT : Term g → Term g
    LEFT  : Term g → Term g
    RIGHT : Term g → Term g
    CASE  : Term g → Term (suc g) → Term (suc g) → Term g
    TRUE  : Term g
    FALSE : Term g
    IF    : Term g → Term g → Term g → Term g


Terms : Nat → Nat → Set
Terms g n = Vec (Term g) n


--------------------------------------------------------------------------------


REN : ∀ {g g′} → g′ ≥ g → Term g
               → Term g′
REN e (VAR I)      = VAR (REN∋ e I)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (PAIR M N)   = PAIR (REN e M) (REN e N)
REN e (FST M)      = FST (REN e M)
REN e (SND M)      = SND (REN e M)
REN e UNIT         = UNIT
REN e (ABORT M)    = ABORT (REN e M)
REN e (LEFT M)     = LEFT (REN e M)
REN e (RIGHT M)    = RIGHT (REN e M)
REN e (CASE M N O) = CASE (REN e M) (REN (keep e) N) (REN (keep e) O)
REN e TRUE         = TRUE
REN e FALSE        = FALSE
REN e (IF M N O)   = IF (REN e M) (REN e N) (REN e O)


RENS : ∀ {g g′ n} → g′ ≥ g → Terms g n
                  → Terms g′ n
RENS e τ = MAPS (REN e) τ


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


SUB : ∀ {g n} → Terms g n → Term n
              → Term g
SUB τ (VAR I)      = GET τ I
SUB τ (LAM M)      = LAM (SUB (LIFTS τ) M)
SUB τ (APP M N)    = APP (SUB τ M) (SUB τ N)
SUB τ (PAIR M N)   = PAIR (SUB τ M) (SUB τ N)
SUB τ (FST M)      = FST (SUB τ M)
SUB τ (SND M)      = SND (SUB τ M)
SUB τ UNIT         = UNIT
SUB τ (ABORT M)    = ABORT (SUB τ M)
SUB τ (LEFT M)     = LEFT (SUB τ M)
SUB τ (RIGHT M)    = RIGHT (SUB τ M)
SUB τ (CASE M N O) = CASE (SUB τ M) (SUB (LIFTS τ) N) (SUB (LIFTS τ) O)
SUB τ TRUE         = TRUE
SUB τ FALSE        = FALSE
SUB τ (IF M N O)   = IF (SUB τ M) (SUB τ N) (SUB τ O)


SUBS : ∀ {g n m} → Terms g n → Terms n m
                 → Terms g m
SUBS τ υ = MAPS (SUB τ) υ


CUT : ∀ {g} → Term g → Term (suc g)
            → Term g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------
