module STLCTypeCheckingTerms where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import STLCTypes
open import SimpleSTLCTerms


--------------------------------------------------------------------------------


mutual
  data TermL : Nat → Set
    where
      LAM   : ∀ {g} → TermL (suc g) → TermL g
      INFER : ∀ {g} → TermR g → TermL g

  data TermR : Nat → Set
    where
      VAR   : ∀ {g} → Fin g → TermR g
      APP   : ∀ {g} → TermR g → TermL g → TermR g
      CHECK : ∀ {g} → TermL g → Type → TermR g


--------------------------------------------------------------------------------


mutual
  RECOVERL : ∀ {g} → TermL g
                   → Term g
  RECOVERL (LAM M)   = LAM (RECOVERL M)
  RECOVERL (INFER M) = RECOVERR M

  RECOVERR : ∀ {g} → TermR g
                   → Term g
  RECOVERR (VAR I)     = VAR I
  RECOVERR (APP M N)   = APP (RECOVERR M) (RECOVERL N)
  RECOVERR (CHECK M A) = RECOVERL M


--------------------------------------------------------------------------------


mutual
  RENL : ∀ {g g′} → g′ ≥ g → TermL g
                  → TermL g′
  RENL e (LAM M)   = LAM (RENL (keep e) M)
  RENL e (INFER M) = INFER (RENR e M)

  RENR : ∀ {g g′} → g′ ≥ g → TermR g
                  → TermR g′
  RENR e (VAR I)     = VAR (REN∋ e I)
  RENR e (APP M N)   = APP (RENR e M) (RENL e N)
  RENR e (CHECK M A) = CHECK (RENL e M) A


WKR : ∀ {g} → TermR g
            → TermR (suc g)
WKR M = RENR (drop id) M


VZR : ∀ {g} → TermR (suc g)
VZR = VAR zero


--------------------------------------------------------------------------------
