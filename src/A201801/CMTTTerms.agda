module A201801.CMTTTerms where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.AllVec
open import A201801.CMTTScopes


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

      MVAR : ∀ {d g m I} → {σ : Scopes d}
                         → σ ∋⟨ I ⟩ m → Terms σ g m
                         → Term σ g

      BOX : ∀ {d g m} → {σ : Scopes d}
                      → Term σ m
                      → Term σ g

      LETBOX : ∀ {d g m} → {σ : Scopes d}
                         → Term σ g → Term (σ , m) g
                         → Term σ g


  Terms : ∀ {d} → Scopes d → Nat → Nat → Set
  Terms σ g n = Vec (Term σ g) n


Terms* : ∀ {d n} → Scopes d → Scopes n → Set
Terms* σ ρ = All (Term σ) ρ


--------------------------------------------------------------------------------


mutual
  REN : ∀ {d g g′} → {σ : Scopes d}
                   → g′ ≥ g → Term σ g
                   → Term σ g′
  REN e (VAR i)      = VAR (REN∋ e i)
  REN e (LAM M)      = LAM (REN (keep e) M)
  REN e (APP M N)    = APP (REN e M) (REN e N)
  REN e (MVAR i υ)   = MVAR i (RENS e υ)
  REN e (BOX M)      = BOX M
  REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

  RENS : ∀ {d g g′ n} → {σ : Scopes d}
                      → g′ ≥ g → Terms σ g n
                      → Terms σ g′ n
  RENS e ∙       = ∙
  RENS e (τ , M) = RENS e τ , REN e M


--------------------------------------------------------------------------------


mutual
  MREN : ∀ {d d′ e g} → {σ : Scopes d} {σ′ : Scopes d′}
                      → σ′ ⊇⟨ e ⟩ σ → Term σ g
                      → Term σ′ g
  MREN e (VAR i)      = VAR i
  MREN e (LAM M)      = LAM (MREN e M)
  MREN e (APP M N)    = APP (MREN e M) (MREN e N)
  MREN e (MVAR i υ)   = MVAR (ren∋ e i) (MRENS e υ)
  MREN e (BOX M)      = BOX (MREN e M)
  MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)

  MRENS : ∀ {d d′ e g n} → {σ : Scopes d} {σ′ : Scopes d′}
                         → σ′ ⊇⟨ e ⟩ σ → Terms σ g n
                         → Terms σ′ g n
  MRENS e ∙       = ∙
  MRENS e (τ , M) = MRENS e τ , MREN e M


MRENS* : ∀ {d d′ e n} → {σ : Scopes d} {σ′ : Scopes d′} {ρ : Scopes n}
                      → σ′ ⊇⟨ e ⟩ σ → Terms* σ ρ
                      → Terms* σ′ ρ
MRENS* e τ = maps (MREN e) τ


--------------------------------------------------------------------------------


WK : ∀ {d g} → {σ : Scopes d}
             → Term σ g
             → Term σ (suc g)
WK M = REN (drop id) M


VZ : ∀ {d g} → {σ : Scopes d}
             → Term σ (suc g)
VZ = VAR zero


WKS : ∀ {d g n} → {σ : Scopes d}
                → Terms σ g n
                → Terms σ (suc g) n
WKS τ = RENS (drop id) τ


LIFTS : ∀ {d g n} → {σ : Scopes d}
                  → Terms σ g n
                  → Terms σ (suc g) (suc n)
LIFTS τ = WKS τ , VZ


VARS : ∀ {d g g′} → {σ : Scopes d}
                  → g′ ≥ g
                  → Terms σ g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)


IDS : ∀ {d g} → {σ : Scopes d}
              → Terms σ g g
IDS = VARS id


--------------------------------------------------------------------------------


MWK : ∀ {d g m} → {σ : Scopes d}
                → Term σ g
                → Term (σ , m) g
MWK M = MREN (drop id⊇) M


MWKS : ∀ {d g n m} → {σ : Scopes d}
                   → Terms σ g n
                   → Terms (σ , m) g n
MWKS τ = MRENS (drop id⊇) τ


MWKS* : ∀ {d n m} → {σ : Scopes d} {ρ : Scopes n}
                  → Terms* σ ρ
                  → Terms* (σ , m) ρ
MWKS* τ = MRENS* (drop id⊇) τ


MVZ : ∀ {d g m} → {σ : Scopes d}
                → Terms (σ , m) g m
                → Term (σ , m) g
MVZ τ = MVAR zero τ


MLIFTS* : ∀ {d n m} → {σ : Scopes d} {ρ : Scopes n}
                    → Terms* σ ρ
                    → Terms* (σ , m) (ρ , m)
MLIFTS* τ = MWKS* τ , MVZ IDS


MVARS* : ∀ {d d′ e} → {σ : Scopes d} {σ′ : Scopes d′}
                    → σ′ ⊇⟨ e ⟩ σ
                    → Terms* σ′ σ
MVARS* done     = ∙
MVARS* (drop e) = MWKS* (MVARS* e)
MVARS* (keep e) = MLIFTS* (MVARS* e)


MIDS* : ∀ {d} → {σ : Scopes d}
              → Terms* σ σ
MIDS* = MVARS* id⊇


--------------------------------------------------------------------------------


mutual
  SUB : ∀ {d g n} → {σ : Scopes d}
                  → Terms σ g n → Term σ n
                  → Term σ g
  SUB τ (VAR i)      = GET τ i
  SUB τ (LAM M)      = LAM (SUB (LIFTS τ) M)
  SUB τ (APP M N)    = APP (SUB τ M) (SUB τ N)
  SUB τ (MVAR i υ)   = MVAR i (SUBS τ υ)
  SUB τ (BOX M)      = BOX M
  SUB τ (LETBOX M N) = LETBOX (SUB τ M) (SUB (MWKS τ) N)

  SUBS : ∀ {d g n m} → {σ : Scopes d}
                     → Terms σ g n → Terms σ n m
                     → Terms σ g m
  SUBS τ ∙       = ∙
  SUBS τ (υ , M) = SUBS τ υ , SUB τ M


--------------------------------------------------------------------------------


mutual
  MSUB : ∀ {d g n} → {σ : Scopes d} {ρ : Scopes n}
                   → Terms* σ ρ → Term ρ g
                   → Term σ g
  MSUB τ (VAR i)      = VAR i
  MSUB τ (LAM M)      = LAM (MSUB τ M)
  MSUB τ (APP M N)    = APP (MSUB τ M) (MSUB τ N)
  MSUB τ (MVAR i υ)   = SUB (MSUBS τ υ) (get τ i)
  MSUB τ (BOX M)      = BOX (MSUB τ M)
  MSUB τ (LETBOX M N) = LETBOX (MSUB τ M) (MSUB (MLIFTS* τ) N)

  MSUBS : ∀ {d g n m} → {σ : Scopes d} {ρ : Scopes n}
                      → Terms* σ ρ → Terms ρ g m
                      → Terms σ g m
  MSUBS τ ∙       = ∙
  MSUBS τ (υ , M) = MSUBS τ υ , MSUB τ M


MSUBS* : ∀ {d n m} → {σ : Scopes d} {ρ : Scopes n} {π : Scopes m}
                   → Terms* σ ρ → Terms* ρ π
                   → Terms* σ π
MSUBS* τ υ = maps (MSUB τ) υ


--------------------------------------------------------------------------------


UNLAM : ∀ {d g} → {σ : Scopes d}
                → Term σ g
                → Term σ (suc g)
UNLAM M = APP (WK M) VZ


CUT : ∀ {d g} → {σ : Scopes d}
              → Term σ g → Term σ (suc g)
              → Term σ g
CUT M N = SUB (IDS , M) N


PSEUDOCUT : ∀ {d g} → {σ : Scopes d}
                    → Term σ g → Term σ (suc g)
                    → Term σ g
PSEUDOCUT M N = APP (LAM N) M


PSEUDOSUB : ∀ {d g n} → {σ : Scopes d}
                      → Terms σ g n → Term σ n
                      → Term σ g
PSEUDOSUB ∙       M = REN bot≥ M
PSEUDOSUB (τ , L) M = APP (PSEUDOSUB τ (LAM M)) L


EXCH : ∀ {d g} → {σ : Scopes d}
               → Term σ (suc (suc g))
               → Term σ (suc (suc g))
EXCH M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


--------------------------------------------------------------------------------


VAU : ∀ {d g m} → {σ : Scopes d}
                → Term (σ , m) g
                → Term σ (suc g)
VAU M = LETBOX VZ (WK M)


UNVAU : ∀ {d g m} → {σ : Scopes d}
                  → Term σ (suc g)
                  → Term (σ , m) g
UNVAU M = APP (LAM (MWK M)) (BOX (MVZ IDS))


BOXAPP : ∀ {d g m} → {σ : Scopes d}
                 → Term σ g → Term σ g
                 → Term σ g
BOXAPP {m = m} M N = LETBOX {m = m} M (LETBOX (MWK N) (BOX (APP (MWK (MVZ IDS)) (MVZ IDS))))


UNBOX : ∀ {d g m} → {σ : Scopes d}
                  → Term σ g → Terms σ g m
                  → Term σ g
UNBOX M υ = LETBOX M (MVZ (MWKS υ))


REBOX : ∀ {d g m} → {σ : Scopes d}
                  → Term σ g
                  → Term σ g
REBOX {m = m} M = LETBOX {m = m} M (BOX (MVZ IDS))


DUPBOX : ∀ {d g m l} → {σ : Scopes d}
                     → Term σ g
                     → Term σ g
DUPBOX {m = m} {l} M = LETBOX {m = l} M (BOX {m = m} (BOX (MVZ IDS)))


MCUT : ∀ {d g m} → {σ : Scopes d}
                 → Term σ m → Term (σ , m) g
                 → Term σ g
MCUT M N = MSUB (MIDS* , M) N


PSEUDOMCUT : ∀ {d g m} → {σ : Scopes d}
                       → Term σ m → Term (σ , m) g
                       → Term σ g
PSEUDOMCUT M N = LETBOX (BOX M) N


PSEUDOMSUB : ∀ {d g n} → {σ : Scopes d} {ρ : Scopes n}
                       → Terms* σ ρ → Term ρ g
                       → Term σ g
PSEUDOMSUB ∙       M = MREN bot⊇ M
PSEUDOMSUB (τ , L) M = APP (PSEUDOMSUB τ (LAM (VAU M))) (BOX L)


MEXCH : ∀ {d g m l} → {σ : Scopes d}
                    → Term (σ , m , l) g
                    → Term (σ , l , m) g
MEXCH M = UNVAU (UNVAU (EXCH (VAU (VAU M))))


--------------------------------------------------------------------------------
