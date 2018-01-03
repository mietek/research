module StdLPTTTerms where

open import Prelude
open import Fin
open import FinLemmas
open import Vec


-- _⊢_
data Term : Nat → Nat → Set
  where
    VAR    : ∀ {d g} → Fin g → Term d g
    LAM    : ∀ {d g} → Term d (suc g) → Term d g
    APP    : ∀ {d g} → Term d g → Term d g → Term d g
    MVAR   : ∀ {d g} → Fin d → Term d g
    BOX    : ∀ {d g} → Term d zero → Term d g
    LETBOX : ∀ {d g} → Term d g → Term (suc d) g → Term d g


-- ren
REN : ∀ {d g g′} → g′ ≥ g → Term d g
                 → Term d g′
REN e (VAR i)      = VAR (renF e i)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (MVAR i)     = MVAR i
REN e (BOX M)      = BOX M
REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

-- wk
WK : ∀ {d g} → Term d g
             → Term d (suc g)
WK M = REN (drop id≥) M

VZ : ∀ {d g} → Term d (suc g)
VZ = VAR zero


-- idren
idREN : ∀ {d g} → (M : Term d g)
                → REN id≥ M ≡ M
idREN (VAR i)      = VAR & id-renF i
idREN (LAM M)      = LAM & idREN M
idREN (APP M N)    = APP & idREN M ⊗ idREN N
idREN (MVAR i)     = refl
idREN (BOX M)      = refl
idREN (LETBOX M N) = LETBOX & idREN M ⊗ idREN N

-- ren○
assocREN : ∀ {d g g′ g″} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (M : Term d g)
                         → REN e₂ (REN e₁ M) ≡ REN (e₁ ∘≥ e₂) M
assocREN e₁ e₂ (VAR i)      = VAR & comp-renF e₁ e₂ i ⁻¹
assocREN e₁ e₂ (LAM M)      = LAM & assocREN (keep e₁) (keep e₂) M
assocREN e₁ e₂ (APP M N)    = APP & assocREN e₁ e₂ M ⊗ assocREN e₁ e₂ N
assocREN e₁ e₂ (MVAR i)     = refl
assocREN e₁ e₂ (BOX M)      = refl
assocREN e₁ e₂ (LETBOX M N) = LETBOX & assocREN e₁ e₂ M ⊗ assocREN e₁ e₂ N


MREN : ∀ {d d′ g} → d′ ≥ d → Term d g
                  → Term d′ g
MREN e (VAR i)      = VAR i
MREN e (LAM M)      = LAM (MREN e M)
MREN e (APP M N)    = APP (MREN e M) (MREN e N)
MREN e (MVAR i)     = MVAR (renF e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)

MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id≥) M

MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero

idMREN : ∀ {d g} → (M : Term d g)
                 → MREN id≥ M ≡ M
idMREN (VAR i)      = refl
idMREN (LAM M)      = LAM & idMREN M
idMREN (APP M N)    = APP & idMREN M ⊗ idMREN N
idMREN (MVAR i)     = MVAR & id-renF i
idMREN (BOX M)      = BOX & idMREN M
idMREN (LETBOX M N) = LETBOX & idMREN M ⊗ idMREN N

assocMREN : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (M : Term d g)
                          → MREN e₂ (MREN e₁ M) ≡ MREN (e₁ ∘≥ e₂) M
assocMREN e₁ e₂ (VAR i)      = refl
assocMREN e₁ e₂ (LAM M)      = LAM & assocMREN e₁ e₂ M
assocMREN e₁ e₂ (APP M N)    = APP & assocMREN e₁ e₂ M ⊗ assocMREN e₁ e₂ N
assocMREN e₁ e₂ (MVAR i)     = MVAR & comp-renF e₁ e₂ i ⁻¹
assocMREN e₁ e₂ (BOX M)      = BOX & assocMREN e₁ e₂ M
assocMREN e₁ e₂ (LETBOX M N) = LETBOX & assocMREN e₁ e₂ M ⊗ assocMREN (keep e₁) (keep e₂) N

commRENMREN : ∀ {d d′ g g′} → (e₁ : g′ ≥ g) (e₂ : d′ ≥ d) (M : Term d g)
                            → MREN e₂ (REN e₁ M) ≡ REN e₁ (MREN e₂ M)
commRENMREN e₁ e₂ (VAR i)      = refl
commRENMREN e₁ e₂ (LAM M)      = LAM & commRENMREN (keep e₁) e₂ M
commRENMREN e₁ e₂ (APP M N)    = APP & commRENMREN e₁ e₂ M ⊗ commRENMREN e₁ e₂ N
commRENMREN e₁ e₂ (MVAR i)     = refl
commRENMREN e₁ e₂ (BOX M)      = refl
commRENMREN e₁ e₂ (LETBOX M N) = LETBOX & commRENMREN e₁ e₂ M ⊗ commRENMREN e₁ (keep e₂) N


-- _⊢⋆_
Terms : Nat → Nat → Nat → Set
Terms d g x = Vec (Term d g) x


-- _◑_
RENS : ∀ {d g g′ x} → g′ ≥ g → Terms d g x
                    → Terms d g′ x
RENS e ζ = map (REN e) ζ

-- wkₛ
WKS : ∀ {d g x} → Terms d g x
                → Terms d (suc g) x
WKS ζ = RENS (drop id≥) ζ

-- liftₛ
LIFTS : ∀ {d g x} → Terms d g x
                  → Terms d (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ

-- idₛ
IDS : ∀ {g d} → Terms d g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS

-- ⌊_⌋
HYPS : ∀ {d g g′} → g′ ≥ g
                  → Terms d g′ g
HYPS done     = ∙
HYPS (drop e) = WKS (HYPS e)
HYPS (keep e) = LIFTS (HYPS e)


getRENS : ∀ {d g g′ x} → (e : g′ ≥ g) (ζ : Terms d g x) (i : Fin x)
                       → get (RENS e ζ) i ≡ REN e (get ζ i)
getRENS e (ζ , M) zero    = refl
getRENS e (ζ , M) (suc i) = getRENS e ζ i

-- natgetₛ
getWKS : ∀ {d g x} → (ζ : Terms d g x) (i : Fin x)
                   → get (WKS ζ) i ≡ WK (get ζ i)
getWKS ζ i = getRENS (drop id≥) ζ i

-- idgetₛ
getIDS : ∀ {d g} → (i : Fin g)
                 → get (IDS {g} {d}) i ≡ VAR i
getIDS zero    = refl
getIDS (suc i) = getWKS IDS i
               ⦙ WK & getIDS i
               ⦙ VAR & (suc & id-renF i)

-- lid◑
idRENS : ∀ {d g x} → (ζ : Terms d g x)
                   → RENS id≥ ζ ≡ ζ
idRENS ∙       = refl
idRENS (ζ , M) = _,_ & idRENS ζ ⊗ idREN M

assocRENS : ∀ {d g g′ g″ x} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (ζ : Terms d g x)
                            → RENS e₂ (RENS e₁ ζ) ≡ RENS (e₁ ∘≥ e₂) ζ
assocRENS e₁ e₂ ∙       = refl
assocRENS e₁ e₂ (ζ , M) = _,_ & assocRENS e₁ e₂ ζ ⊗ assocREN e₁ e₂ M


MRENS : ∀ {d d′ g x} → d′ ≥ d → Terms d g x
                     → Terms d′ g x
MRENS e ζ = map (MREN e) ζ

MWKS : ∀ {d g x} → Terms d g x
                 → Terms (suc d) g x
MWKS ζ = MRENS (drop id≥) ζ


getMRENS : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (i : Fin x)
                        → get (MRENS e ζ) i ≡ MREN e (get ζ i)
getMRENS e (ζ , M) zero    = refl
getMRENS e (ζ , M) (suc i) = getMRENS e ζ i

getMWKS : ∀ {d g x} → (ζ : Terms d g x) (i : Fin x)
                    → get (MWKS ζ) i ≡ MWK (get ζ i)
getMWKS ζ i = getMRENS (drop id≥) ζ i

idMRENS : ∀ {d g x} → (ζ : Terms d g x)
                    → MRENS id≥ ζ ≡ ζ
idMRENS ∙       = refl
idMRENS (ζ , M) = _,_ & idMRENS ζ ⊗ idMREN M

assocMRENS : ∀ {d d′ d″ g x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms d g x)
                             → MRENS e₂ (MRENS e₁ ζ) ≡ MRENS (e₁ ∘≥ e₂) ζ
assocMRENS e₁ e₂ ∙       = refl
assocMRENS e₁ e₂ (ζ , M) = _,_ & assocMRENS e₁ e₂ ζ ⊗ assocMREN e₁ e₂ M

commRENSMRENS : ∀ {d d′ g g′ x} → (e₁ : g′ ≥ g) (e₂ : d′ ≥ d) (ζ : Terms d g x)
                                → MRENS e₂ (RENS e₁ ζ) ≡ RENS e₁ (MRENS e₂ ζ)
commRENSMRENS e₁ e₂ ∙       = refl
commRENSMRENS e₁ e₂ (ζ , M) = _,_ & commRENSMRENS e₁ e₂ ζ ⊗ commRENMREN e₁ e₂ M


-- sub
SUB : ∀ {d g x} → Terms d g x → Term d x
                → Term d g
SUB ζ (VAR i)      = get ζ i
SUB ζ (LAM M)      = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N)    = APP (SUB ζ M) (SUB ζ N)
SUB ζ (MVAR i)     = MVAR i
SUB ζ (BOX M)      = BOX M
SUB ζ (LETBOX M N) = LETBOX (SUB ζ M) (SUB (MWKS ζ) N)

-- cut
CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


xgetWKS : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (i : Fin x)
                       → get (MRENS e (WKS ζ)) i ≡ MREN e (WK (get ζ i))
xgetWKS e (ζ , M) zero    = refl
xgetWKS e (ζ , N) (suc i) = xgetWKS e ζ i

xgetIDS : ∀ {d d′ g} → (e : d′ ≥ d) (i : Fin g)
                     → get (MRENS e IDS) i ≡ VAR i
xgetIDS e zero    = refl
xgetIDS e (suc i) = xgetWKS e IDS i
                  ⦙ commRENMREN (drop id≥) e (get IDS i)
                  ⦙ REN (drop id≥) & getMRENS e IDS i ⁻¹
                  ⦙ WK & xgetIDS e i
                  ⦙ VAR & (suc & id-renF i)


huh : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
                 → MWK (MREN e M) ≡ MREN (keep e) (MWK M)
huh e (VAR i)      = refl
huh e (LAM M)      = LAM & huh e M
huh e (APP M N)    = APP & huh e M ⊗ huh e N
huh e (MVAR i)     = MVAR & ( suc & ( id-renF (renF e i)
                                    ⦙ renF e & id-renF i ⁻¹
                                    )
                            )
huh e (BOX M)      = BOX & huh e M
huh e (LETBOX M N) = LETBOX & huh e M ⊗ ( assocMREN (keep e) (keep (drop id≥)) N
                                        ⦙ ( assocMREN (keep (drop id≥)) (keep (keep e)) N
                                          ⦙ (\ e′ → MREN (keep (drop e′)) N)
                                            & (lid-∘≥ e ⦙ rid-∘≥ e ⁻¹)
                                          ) ⁻¹
                                        )

huhs : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x)
                    → MWKS (MRENS e ζ) ≡ MRENS (keep e) (MWKS ζ)
huhs e ∙       = refl
huhs e (ζ , M) = _,_ & huhs e ζ ⊗ huh e M

-- wut : ∀ {d d′ g} → (e : d′ ≥ d)
--                  → MWKS (MRENS e (IDS {g})) ≡ MRENS (keep e) IDS
-- wut e = {!huhs e IDS!}

-- oops : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (M : Term d′ x)
--                     → SUB (MRENS e ζ) M ≡ {!!}
-- oops e ζ (VAR i)      = {!!}
-- oops e ζ (LAM M)      = {!!}
-- oops e ζ (APP M N)    = {!!}
-- oops e ζ (MVAR i)     = {!!}
-- oops e ζ (BOX M)      = {!!}
-- oops e ζ (LETBOX M N) = {!!}


-- xidSUB : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d′ g)
--                     → SUB (MRENS e IDS) M ≡ M
-- xidSUB e (VAR i)      = xgetIDS e i
-- xidSUB e (LAM M)      = LAM & ( (\ ζ → SUB ζ M)
--                                 & ( (_, VZ)
--                                     & commRENSMRENS (drop id≥) e IDS
--                                   ) ⁻¹
--                               ⦙ xidSUB e M
--                               )
-- xidSUB e (APP M N)    = APP & xidSUB e M ⊗ xidSUB e N
-- xidSUB e (MVAR i)     = refl
-- xidSUB e (BOX M)      = refl
-- xidSUB e (LETBOX M N) = LETBOX & xidSUB e M ⊗ {!!}
-- -- xidSUB e (LETBOX M N) = LETBOX & xidSUB e M ⊗ ( (\ ζ → SUB ζ N)
-- --                                                 & huhs e IDS
-- --                                                 ⦙ {!(\ !}
-- --                                               ⦙ xidSUB (keep e) N
-- --                                               )


-- idsub
postulate
  idSUB : ∀ {d g} → (M : Term d g)
                  → SUB IDS M ≡ M
-- idSUB (VAR i)      = getIDS i
-- idSUB (LAM M)      = LAM & idSUB M
-- idSUB (APP M N)    = APP & idSUB M ⊗ idSUB N
-- idSUB (MVAR i)     = refl
-- idSUB (BOX M)      = refl
-- idSUB {d} {g} (LETBOX M N) = LETBOX & idSUB M ⊗ {!idSUB N!}


-- _●_
SUBS : ∀ {d g x p} → Terms d g x → Terms d x p
                   → Terms d g p
SUBS ζ φ = map (SUB ζ) φ


Term₁ : Nat → Set
Term₁ d = Term d zero

Terms₁ : Nat → Nat → Set
Terms₁ d x = Vec (Term₁ d) x


MRENS₁ : ∀ {d d′ x} → d′ ≥ d → Terms₁ d x
                    → Terms₁ d′ x
MRENS₁ e ζ = MRENS e ζ

MWKS₁ : ∀ {d x} → Terms₁ d x
                → Terms₁ (suc d) x
MWKS₁ ζ = MWKS ζ

MLIFTS₁ : ∀ {d x} → Terms₁ d x
                  → Terms₁ (suc d) (suc x)
MLIFTS₁ ζ = MWKS₁ ζ , MVZ

MIDS₁ : ∀ {d} → Terms₁ d d
MIDS₁ {zero}  = ∙
MIDS₁ {suc d} = MLIFTS₁ MIDS₁

MHYPS₁ : ∀ {d d′} → d′ ≥ d
                  → Terms₁ d′ d
MHYPS₁ done     = ∙
MHYPS₁ (drop e) = MWKS₁ (MHYPS₁ e)
MHYPS₁ (keep e) = MLIFTS₁ (MHYPS₁ e)


getMRENS₁ : ∀ {d d′ x} → (e : d′ ≥ d) (ζ : Terms₁ d x) (i : Fin x)
                       → get (MRENS₁ e ζ) i ≡ MREN e (get ζ i)
getMRENS₁ e (ζ , M) zero    = refl
getMRENS₁ e (ζ , M) (suc i) = getMRENS₁ e ζ i

getMWKS₁ : ∀ {d x} → (ζ : Terms₁ d x) (i : Fin x)
                   → get (MWKS ζ) i ≡ MWK (get ζ i)
getMWKS₁ ζ i = getMRENS (drop id≥) ζ i

getMIDS₁ : ∀ {d} → (i : Fin d)
                 → get (MIDS₁ {d}) i ≡ MVAR i
getMIDS₁ zero    = refl
getMIDS₁ (suc i) = getMWKS₁ MIDS₁ i
                 ⦙ MWK & getMIDS₁ i
                 ⦙ MVAR & (suc & id-renF i)

idMRENS₁ : ∀ {d x} → (ζ : Terms₁ d x)
                   → MRENS₁ id≥ ζ ≡ ζ
idMRENS₁ ζ = idMRENS ζ

assocMRENS₁ : ∀ {d d′ d″ x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms₁ d x)
                            → MRENS₁ e₂ (MRENS₁ e₁ ζ) ≡ MRENS₁ (e₁ ∘≥ e₂) ζ
assocMRENS₁ e₁ e₂ ζ = assocMRENS e₁ e₂ ζ


MSUB : ∀ {d g x} → Terms₁ d x → Term x g
                 → Term d g
MSUB ζ (VAR i)      = VAR i
MSUB ζ (LAM M)      = LAM (MSUB ζ M)
MSUB ζ (APP M N)    = APP (MSUB ζ M) (MSUB ζ N)
MSUB ζ (MVAR i)     = SUB ∙ (get ζ i)
MSUB ζ (BOX M)      = BOX (MSUB ζ M)
MSUB ζ (LETBOX M N) = LETBOX (MSUB ζ M) (MSUB (MLIFTS₁ ζ) N)

MCUT : ∀ {d g} → Term₁ d → Term (suc d) g
               → Term d g
MCUT M N = MSUB (MIDS₁ , M) N

postulate
  idMSUB : ∀ {d g} → (M : Term d g)
                   → MSUB MIDS₁ M ≡ M
-- idMSUB (VAR i)      = refl
-- idMSUB (LAM M)      = LAM & idMSUB M
-- idMSUB (APP M N)    = APP & idMSUB M ⊗ idMSUB N
-- idMSUB (MVAR i)     = {!!}
-- idMSUB (BOX M)      = BOX & idMSUB M
-- idMSUB (LETBOX M N) = LETBOX & idMSUB M ⊗ idMSUB N

-- assocMSUBMREN : ∀ {d g x x′} → (e : x′ ≥ x) (ζ : Terms₁ d x′) (M : Term x g)
--                              → MSUB ζ (MREN e M) ≡ MSUB {!!} M
-- assocMSUBMREN = {!!}

-- MSUBₚ (MIDS₁ , MREN e O) (MRENₚ (keep e) B) != MRENₚ e .A

-- assocMSUBMREN : ∀ {d d′ g x} →
--                              →


UNLAM : ∀ {d g} → Term d g
                → Term d (suc g)
UNLAM M = APP (WK M) VZ

SHL : ∀ {d g} → Term d (suc g)
              → Term (suc d) g
SHL M = APP (LAM (MWK M)) (BOX MVZ)

SHR : ∀ {d g} → Term (suc d) g
              → Term d (suc g)
SHR M = LETBOX VZ (WK M)

EX : ∀ {d g} → Term d (suc (suc g))
             → Term d (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)

MEX : ∀ {d g} → Term (suc (suc d)) g
              → Term (suc (suc d)) g
MEX M = SHL (SHL (EX (SHR (SHR M))))
