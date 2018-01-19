module STLCBidirectionalTermsForTypeChecking where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import STLCTypes


--------------------------------------------------------------------------------


mutual
  data Termₗ : Nat → Set
    where
      LAM : ∀ {g} → Termₗ (suc g) → Termₗ g
      INF : ∀ {g} → Termᵣ g → Termₗ g

  data Termᵣ : Nat → Set
    where
      VAR : ∀ {g} → Fin g → Termᵣ g
      APP : ∀ {g} → Termᵣ g → Termₗ g → Termᵣ g
      CHK : ∀ {g} → Termₗ g → Type → Termᵣ g


--------------------------------------------------------------------------------


mutual
  RENₗ : ∀ {g g′} → g′ ≥ g → Termₗ g
                  → Termₗ g′
  RENₗ e (LAM M) = LAM (RENₗ (keep e) M)
  RENₗ e (INF M) = INF (RENᵣ e M)

  RENᵣ : ∀ {g g′} → g′ ≥ g → Termᵣ g
                  → Termᵣ g′
  RENᵣ e (VAR I)   = VAR (REN∋ e I)
  RENᵣ e (APP M N) = APP (RENᵣ e M) (RENₗ e N)
  RENᵣ e (CHK M A) = CHK (RENₗ e M) A


WKᵣ : ∀ {g} → Termᵣ g
            → Termᵣ (suc g)
WKᵣ M = RENᵣ (drop id) M


VZᵣ : ∀ {g} → Termᵣ (suc g)
VZᵣ = VAR zero


--------------------------------------------------------------------------------
