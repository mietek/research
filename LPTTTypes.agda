module LPTTTypes where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import S4TTTerms
open import S4TTTermsLemmas


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Type : Nat → Set
  where
    ι_   : ∀ {d} → String → Type d
    _⊃_  : ∀ {d} → Type d → Type d → Type d
    [_]_ : ∀ {d} → Term d zero → Type d → Type d


instance
  TypeVar : ∀ {d} → IsString (Type d)
  TypeVar =
    record
      { Constraint = \ s → 𝟙
      ; fromString = \ s → ι s
      }


Types : Nat → Nat → Set
Types d g = Vec (Type d) g


--------------------------------------------------------------------------------


TMREN : ∀ {d d′} → d′ ≥ d → Type d
                 → Type d′
TMREN e (ι P)     = ι P
TMREN e (A ⊃ B)   = TMREN e A ⊃ TMREN e B
TMREN e ([ M ] A) = [ MREN e M ] TMREN e A


TMRENS : ∀ {d d′ n} → d′ ≥ d → Types d n
                    → Types d′ n
TMRENS e Ξ = MAPS (TMREN e) Ξ


--------------------------------------------------------------------------------


TMWK : ∀ {d} → Type d
             → Type (suc d)
TMWK A = TMREN (drop id) A


TMWKS : ∀ {d n} → Types d n
                → Types (suc d) n
TMWKS Ξ = TMRENS (drop id) Ξ


--------------------------------------------------------------------------------


TMSUB : ∀ {d n} → Terms* d n → Type n
                → Type d
TMSUB τ (ι P)     = ι P
TMSUB τ (A ⊃ B)   = TMSUB τ A ⊃ TMSUB τ B
TMSUB τ ([ M ] A) = [ MSUB τ M ] TMSUB τ A


TMSUBS : ∀ {d n m} → Terms* d n → Types n m
                   → Types d m
TMSUBS τ Ξ = MAPS (TMSUB τ) Ξ


--------------------------------------------------------------------------------


TMCUT : ∀ {d} → Term d zero → Type (suc d)
              → Type d
TMCUT M A = TMSUB (MIDS* , M) A


--------------------------------------------------------------------------------
