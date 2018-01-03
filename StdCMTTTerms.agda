module StdCMTTTerms where

open import Prelude
open import Fin
open import Vec
open import VecOrnaments


--------------------------------------------------------------------------------


Scopes : Nat → Set
Scopes d = Vec Nat d


--------------------------------------------------------------------------------


mutual
  data Term : ∀ {d} → Scopes d → Nat → Set
    where
      VAR : ∀ {d g} → {σ : Scopes d}
                    → Fin g
                    → Term σ g

      LAM : ∀ {d g} → {σ : Scopes d}
                    → Term σ (suc g)
                    → Term σ g

      APP : ∀ {d g} → {σ : Scopes d}
                    → Term σ g → Term σ g
                    → Term σ g

      MVAR : ∀ {p d g i} → {σ : Scopes d}
                         → σ ∋⟨ i ⟩ p → Terms σ g p
                         → Term σ g

      BOX : ∀ {p d g} → {σ : Scopes d}
                      → Term σ p
                      → Term σ g

      LETBOX : ∀ {p d g} → {σ : Scopes d}
                         → Term σ g → Term (σ , p) g
                         → Term σ g

  Terms : ∀ {d} → Scopes d → Nat → Nat → Set
  Terms σ g x = Vec (Term σ g) x


--------------------------------------------------------------------------------


mutual
  REN : ∀ {d g g′} → {σ : Scopes d}
                   → g′ ≥ g → Term σ g
                   → Term σ g′
  REN e (VAR i)      = VAR (renF e i)
  REN e (LAM M)      = LAM (REN (keep e) M)
  REN e (APP M N)    = APP (REN e M) (REN e N)
  REN e (MVAR 𝒾 φ)   = MVAR 𝒾 (RENS e φ)
  REN e (BOX M)      = BOX M
  REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

  RENS : ∀ {d g g′ x} → {σ : Scopes d}
                      → g′ ≥ g → Terms σ g x
                      → Terms σ g′ x
  RENS e ∙       = ∙
  RENS e (ζ , M) = RENS e ζ , REN e M
  -- NOTE: Equivalent to
  -- RENS e ζ = map (REN e) ζ


WK : ∀ {d g} → {σ : Scopes d}
             → Term σ g
             → Term σ (suc g)
WK M = REN (drop id≥) M


VZ : ∀ {d g} → {σ : Scopes d}
             → Term σ (suc g)
VZ = VAR zero


WKS : ∀ {d g x} → {σ : Scopes d}
                → Terms σ g x
                → Terms σ (suc g) x
WKS ζ = RENS (drop id≥) ζ


LIFTS : ∀ {d g x} → {σ : Scopes d}
                  → Terms σ g x
                  → Terms σ (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ


IDS : ∀ {g d} → {σ : Scopes d}
              → Terms σ g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


--------------------------------------------------------------------------------


mutual
  MREN : ∀ {d d′ e g} → {σ : Scopes d} {σ′ : Scopes d′}
                      → σ′ ⊇⟨ e ⟩ σ → Term σ g
                      → Term σ′ g
  MREN η (VAR i)      = VAR i
  MREN η (LAM M)      = LAM (MREN η M)
  MREN η (APP M N)    = APP (MREN η M) (MREN η N)
  MREN η (MVAR 𝒾 φ)   = MVAR (ren∋ η 𝒾) (MRENS η φ)
  MREN η (BOX M)      = BOX (MREN η M)
  MREN η (LETBOX M N) = LETBOX (MREN η M) (MREN (keep η) N)

  MRENS : ∀ {d d′ e g x} → {σ : Scopes d} {σ′ : Scopes d′}
                         → σ′ ⊇⟨ e ⟩ σ → Terms σ g x
                         → Terms σ′ g x
  MRENS η ∙       = ∙
  MRENS η (ζ , M) = MRENS η ζ , MREN η M
  -- NOTE: Equivalent to
  -- MRENS η ζ = map (MREN η) ζ


MWK : ∀ {p d g} → {σ : Scopes d}
                → Term σ g
                → Term (σ , p) g
MWK M = MREN (drop id⊇) M


MWKS : ∀ {p d g x} → {σ : Scopes d}
                   → Terms σ g x
                   → Terms (σ , p) g x
MWKS ζ = MRENS (drop id⊇) ζ


MVZ : ∀ {p d g} → {σ : Scopes d}
                → Terms σ g p
                → Term (σ , p) g
MVZ φ = MVAR zero (MWKS φ)


--------------------------------------------------------------------------------


mutual
  SUB : ∀ {d g x} → {σ : Scopes d}
                  → Terms σ g x → Term σ x
                  → Term σ g
  SUB ζ (VAR i)      = get ζ i
  SUB ζ (LAM M)      = LAM (SUB (LIFTS ζ) M)
  SUB ζ (APP M N)    = APP (SUB ζ M) (SUB ζ N)
  SUB ζ (MVAR 𝒾 φ)   = MVAR 𝒾 (SUBS ζ φ)
  SUB ζ (BOX M)      = BOX M
  SUB ζ (LETBOX M N) = LETBOX (SUB ζ M) (SUB (MWKS ζ) N)

  SUBS : ∀ {d g x p} → {σ : Scopes d}
                     → Terms σ g x → Terms σ x p
                     → Terms σ g p
  SUBS ζ ∙       = ∙
  SUBS ζ (φ , M) = SUBS ζ φ , SUB ζ M
  -- NOTE: Equivalent to
  -- SUBS ζ φ = map (SUB ζ) φ


CUT : ∀ {d g} → {σ : Scopes d}
              → Term σ g → Term σ (suc g)
              → Term σ g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------


Term₁ : ∀ {d} → Scopes d → Nat → Set
Term₁ σ p = Term σ p


Terms₁ : ∀ {d x} → Scopes d → Scopes x → Set
Terms₁ σ ξ = All (Term₁ σ) ξ


--------------------------------------------------------------------------------


MRENS₁ : ∀ {d d′ e x} → {σ : Scopes d} {σ′ : Scopes d′} {ξ : Scopes x}
                      → σ′ ⊇⟨ e ⟩ σ → Terms₁ σ ξ
                      → Terms₁ σ′ ξ
MRENS₁ e ζ = mapAll (MREN e) ζ


MWKS₁ : ∀ {p d x} → {σ : Scopes d} {ξ : Scopes x}
                  → Terms₁ σ ξ
                  → Terms₁ (σ , p) ξ
MWKS₁ ζ = MRENS₁ (drop id⊇) ζ


MLIFTS₁ : ∀ {p d x} → {σ : Scopes d} {ξ : Scopes x}
                    → Terms₁ σ ξ
                    → Terms₁ (σ , p) (ξ , p)
MLIFTS₁ ζ = MWKS₁ ζ , MVZ IDS


MIDS₁ : ∀ {d} → {σ : Scopes d}
              → Terms₁ σ σ
MIDS₁ {σ = ∙}     = ∙
MIDS₁ {σ = σ , p} = MLIFTS₁ MIDS₁


--------------------------------------------------------------------------------


mutual
  MSUB : ∀ {d g x} → {σ : Scopes d} {ξ : Scopes x}
                   → Terms₁ σ ξ → Term ξ g
                   → Term σ g
  MSUB ζ (VAR i)      = VAR i
  MSUB ζ (LAM M)      = LAM (MSUB ζ M)
  MSUB ζ (APP M N)    = APP (MSUB ζ M) (MSUB ζ N)
  MSUB ζ (MVAR 𝒾 φ)   = SUB (MSUBS ζ φ) (lookup ζ 𝒾)
  MSUB ζ (BOX M)      = BOX (MSUB ζ M)
  MSUB ζ (LETBOX M N) = LETBOX (MSUB ζ M) (MSUB (MLIFTS₁ ζ) N)

  MSUBS : ∀ {d g x p} → {σ : Scopes d} {ξ : Scopes x}
                      → Terms₁ σ ξ → Terms ξ g p
                      → Terms σ g p
  MSUBS ζ ∙       = ∙
  MSUBS ζ (φ , M) = MSUBS ζ φ , MSUB ζ M
  -- NOTE: Equivalent to
  -- MSUBS ζ φ = map (MSUB ζ) φ


MCUT : ∀ {p d g} → {σ : Scopes d}
                 → Term₁ σ p → Term (σ , p) g
                 → Term σ g
MCUT M N = MSUB (MIDS₁ , M) N


--------------------------------------------------------------------------------


UNLAM : ∀ {d g} → {σ : Scopes d}
                → Term σ g
                → Term σ (suc g)
UNLAM M = APP (WK M) VZ


EX : ∀ {d g} → {σ : Scopes d}
             → Term σ (suc (suc g))
             → Term σ (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------


SHL : ∀ {p d g} → {σ : Scopes d}
                → Term σ (suc g)
                → Term (σ , p) g
SHL M = APP (LAM (MWK M)) (BOX (MVZ IDS))


SHR : ∀ {p d g} → {σ : Scopes d}
                → Term (σ , p) g
                → Term σ (suc g)
SHR M = LETBOX VZ (WK M)


MEX : ∀ {p q d g} → {σ : Scopes d}
                  → Term (σ , p , q) g
                  → Term (σ , q , p) g
MEX M = SHL (SHL (EX (SHR (SHR M))))


--------------------------------------------------------------------------------
