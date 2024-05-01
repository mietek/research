module A201801.StdCMTTTerms where

open import A201801.Prelude
open import A201801.Fin
open import A201801.Vec
open import A201801.AllVec


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

      MVAR : ∀ {m d g i} → {σ : Scopes d}
                         → σ ∋⟨ i ⟩ m → Terms σ g m
                         → Term σ g

      BOX : ∀ {m d g} → {σ : Scopes d}
                      → Term σ m
                      → Term σ g

      LETBOX : ∀ {m d g} → {σ : Scopes d}
                         → Term σ g → Term (σ , m) g
                         → Term σ g

  Terms : ∀ {d} → Scopes d → Nat → Nat → Set
  Terms σ g n = Vec (Term σ g) n


--------------------------------------------------------------------------------


mutual
  REN : ∀ {d g g′} → {σ : Scopes d}
                   → g′ ≥ g → Term σ g
                   → Term σ g′
  REN e (VAR i)      = VAR (REN∋ e i)
  REN e (LAM M)      = LAM (REN (keep e) M)
  REN e (APP M N)    = APP (REN e M) (REN e N)
  REN e (MVAR 𝒾 y)   = MVAR 𝒾 (RENS e y)
  REN e (BOX M)      = BOX M
  REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

  RENS : ∀ {d g g′ n} → {σ : Scopes d}
                      → g′ ≥ g → Terms σ g n
                      → Terms σ g′ n
  RENS e ∙       = ∙
  RENS e (x , M) = RENS e x , REN e M
  -- NOTE: Equivalent to
  -- RENS e x = maps (REN e) x


--------------------------------------------------------------------------------


WK : ∀ {d g} → {σ : Scopes d}
             → Term σ g
             → Term σ (suc g)
WK M = REN (drop id≥) M


VZ : ∀ {d g} → {σ : Scopes d}
             → Term σ (suc g)
VZ = VAR zero


WKS : ∀ {d g n} → {σ : Scopes d}
                → Terms σ g n
                → Terms σ (suc g) n
WKS x = RENS (drop id≥) x


LIFTS : ∀ {d g n} → {σ : Scopes d}
                  → Terms σ g n
                  → Terms σ (suc g) (suc n)
LIFTS x = WKS x , VZ


VARS : ∀ {d g g′} → {σ : Scopes d}
                  → g′ ≥ g
                  → Terms σ g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)


IDS : ∀ {d g} → {σ : Scopes d}
              → Terms σ g g
IDS = VARS id≥


--------------------------------------------------------------------------------


mutual
  MREN : ∀ {d d′ e g} → {σ : Scopes d} {σ′ : Scopes d′}
                      → σ′ ⊇⟨ e ⟩ σ → Term σ g
                      → Term σ′ g
  MREN η (VAR i)      = VAR i
  MREN η (LAM M)      = LAM (MREN η M)
  MREN η (APP M N)    = APP (MREN η M) (MREN η N)
  MREN η (MVAR 𝒾 y)   = MVAR (ren∋ η 𝒾) (MRENS η y)
  MREN η (BOX M)      = BOX (MREN η M)
  MREN η (LETBOX M N) = LETBOX (MREN η M) (MREN (keep η) N)

  MRENS : ∀ {d d′ e g n} → {σ : Scopes d} {σ′ : Scopes d′}
                         → σ′ ⊇⟨ e ⟩ σ → Terms σ g n
                         → Terms σ′ g n
  MRENS η ∙       = ∙
  MRENS η (x , M) = MRENS η x , MREN η M
  -- NOTE: Equivalent to
  -- MRENS η x = maps (MREN η) x


--------------------------------------------------------------------------------


MWK : ∀ {m d g} → {σ : Scopes d}
                → Term σ g
                → Term (σ , m) g
MWK M = MREN (drop id⊇) M


MWKS : ∀ {m d g n} → {σ : Scopes d}
                   → Terms σ g n
                   → Terms (σ , m) g n
MWKS x = MRENS (drop id⊇) x


MVZ : ∀ {m d g} → {σ : Scopes d}
                → Terms σ g m
                → Term (σ , m) g
MVZ y = MVAR zero (MWKS y)


--------------------------------------------------------------------------------


mutual
  SUB : ∀ {d g n} → {σ : Scopes d}
                  → Terms σ g n → Term σ n
                  → Term σ g
  SUB x (VAR i)      = GET x i
  SUB x (LAM M)      = LAM (SUB (LIFTS x) M)
  SUB x (APP M N)    = APP (SUB x M) (SUB x N)
  SUB x (MVAR 𝒾 y)   = MVAR 𝒾 (SUBS x y)
  SUB x (BOX M)      = BOX M
  SUB x (LETBOX M N) = LETBOX (SUB x M) (SUB (MWKS x) N)

  SUBS : ∀ {d g n m} → {σ : Scopes d}
                     → Terms σ g n → Terms σ n m
                     → Terms σ g m
  SUBS x ∙       = ∙
  SUBS x (y , M) = SUBS x y , SUB x M
  -- NOTE: Equivalent to
  -- SUBS x y = maps (SUB x) y


CUT : ∀ {d g} → {σ : Scopes d}
              → Term σ g → Term σ (suc g)
              → Term σ g
CUT M N = SUB (IDS , M) N


--------------------------------------------------------------------------------


Term₁ : ∀ {d} → Scopes d → Nat → Set
Term₁ σ m = Term σ m


Terms₁ : ∀ {d n} → Scopes d → Scopes n → Set
Terms₁ σ τ = All (Term₁ σ) τ


--------------------------------------------------------------------------------


MRENS₁ : ∀ {d d′ e n} → {σ : Scopes d} {σ′ : Scopes d′} {τ : Scopes n}
                      → σ′ ⊇⟨ e ⟩ σ → Terms₁ σ τ
                      → Terms₁ σ′ τ
MRENS₁ e x = maps (MREN e) x


MWKS₁ : ∀ {m d n} → {σ : Scopes d} {τ : Scopes n}
                  → Terms₁ σ τ
                  → Terms₁ (σ , m) τ
MWKS₁ x = MRENS₁ (drop id⊇) x


MLIFTS₁ : ∀ {m d n} → {σ : Scopes d} {τ : Scopes n}
                    → Terms₁ σ τ
                    → Terms₁ (σ , m) (τ , m)
MLIFTS₁ x = MWKS₁ x , MVZ IDS


MVARS₁ : ∀ {d d′ e} → {σ : Scopes d} {σ′ : Scopes d′}
                    → σ′ ⊇⟨ e ⟩ σ
                    → Terms₁ σ′ σ
MVARS₁ done     = ∙
MVARS₁ (drop η) = MWKS₁ (MVARS₁ η)
MVARS₁ (keep η) = MLIFTS₁ (MVARS₁ η)


MIDS₁ : ∀ {d} → {σ : Scopes d}
              → Terms₁ σ σ
MIDS₁ = MVARS₁ id⊇


--------------------------------------------------------------------------------


mutual
  MSUB : ∀ {d g n} → {σ : Scopes d} {τ : Scopes n}
                   → Terms₁ σ τ → Term τ g
                   → Term σ g
  MSUB x (VAR i)      = VAR i
  MSUB x (LAM M)      = LAM (MSUB x M)
  MSUB x (APP M N)    = APP (MSUB x M) (MSUB x N)
  MSUB x (MVAR 𝒾 y)   = SUB (MSUBS x y) (get x 𝒾)
  MSUB x (BOX M)      = BOX (MSUB x M)
  MSUB x (LETBOX M N) = LETBOX (MSUB x M) (MSUB (MLIFTS₁ x) N)

  MSUBS : ∀ {d g n m} → {σ : Scopes d} {τ : Scopes n}
                      → Terms₁ σ τ → Terms τ g m
                      → Terms σ g m
  MSUBS x ∙       = ∙
  MSUBS x (y , M) = MSUBS x y , MSUB x M
  -- NOTE: Equivalent to
  -- MSUBS x y = maps (MSUB x) y


MCUT : ∀ {m d g} → {σ : Scopes d}
                 → Term₁ σ m → Term (σ , m) g
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


UP : ∀ {m d g} → {σ : Scopes d}
               → Term σ (suc g)
               → Term (σ , m) g
UP M = APP (LAM (MWK M)) (BOX (MVZ IDS))


DOWN : ∀ {m d g} → {σ : Scopes d}
                 → Term (σ , m) g
                 → Term σ (suc g)
DOWN M = LETBOX VZ (WK M)


MEX : ∀ {m o d g} → {σ : Scopes d}
                  → Term (σ , m , o) g
                  → Term (σ , o , m) g
MEX M = UP (UP (EX (DOWN (DOWN M))))


--------------------------------------------------------------------------------
