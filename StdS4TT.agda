module StdS4TT where

open import Prelude
open import Fin
open import Vec


data Term : Nat → Nat → Set
  where
    VAR    : ∀ {d g} → Fin g → Term d g
    LAM    : ∀ {d g} → Term d (suc g) → Term d g
    APP    : ∀ {d g} → Term d g → Term d g → Term d g
    MVAR   : ∀ {d g} → Fin d → Term d g
    BOX    : ∀ {d g} → Term d zero → Term d g
    LETBOX : ∀ {d g} → Term d g → Term (suc d) g → Term d g


REN : ∀ {d g g′} → g′ ≥ g → Term d g
                 → Term d g′
REN e (VAR i)      = VAR (renFin e i)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (MVAR i)     = MVAR i
REN e (BOX M)      = BOX M
REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

WK : ∀ {d g} → Term d g
             → Term d (suc g)
WK M = REN (drop id≥) M

VZ : ∀ {d g} → Term d (suc g)
VZ = VAR zero


MREN : ∀ {d d′ g} → d′ ≥ d → Term d g
                  → Term d′ g
MREN e (VAR i)      = VAR i
MREN e (LAM M)      = LAM (MREN e M)
MREN e (APP M N)    = APP (MREN e M) (MREN e N)
MREN e (MVAR i)     = MVAR (renFin e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)

MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id≥) M

MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero


Terms : Nat → Nat → Nat → Set
Terms d g x = Vec (Term d g) x


RENS : ∀ {d g g′ x} → g′ ≥ g → Terms d g x
                    → Terms d g′ x
RENS e ζ = map (REN e) ζ

WKS : ∀ {d g x} → Terms d g x
                → Terms d (suc g) x
WKS ζ = RENS (drop id≥) ζ

LIFTS : ∀ {d g x} → Terms d g x
                  → Terms d (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ

IDS : ∀ {g d} → Terms d g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


MRENS : ∀ {d d′ g x} → d′ ≥ d → Terms d g x
                     → Terms d′ g x
MRENS e ζ = map (MREN e) ζ

MWKS : ∀ {d g x} → Terms d g x
                 → Terms (suc d) g x
MWKS ζ = MRENS (drop id≥) ζ


SUB : ∀ {d g x} → Terms d g x → Term d x
                → Term d g
SUB ζ (VAR i)      = get ζ i
SUB ζ (LAM M)      = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N)    = APP (SUB ζ M) (SUB ζ N)
SUB ζ (MVAR i)     = MVAR i
SUB ζ (BOX M)      = BOX M
SUB ζ (LETBOX M N) = LETBOX (SUB ζ M) (SUB (MWKS ζ) N)

CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


Term₁ : Nat → Set
Term₁ d = Term d zero

Terms₁ : Nat → Nat → Set
Terms₁ d x = Vec (Term₁ d) x


MRENS₁ : ∀ {d d′ x} → d′ ≥ d → Terms₁ d x
                    → Terms₁ d′ x
MRENS₁ e ζ = map (MREN e) ζ

MWKS₁ : ∀ {d x} → Terms₁ d x
                → Terms₁ (suc d) x
MWKS₁ ζ = MRENS₁ (drop id≥) ζ

MLIFTS₁ : ∀ {d x} → Terms₁ d x
                  → Terms₁ (suc d) (suc x)
MLIFTS₁ ζ = MWKS₁ ζ , MVZ

MIDS₁ : ∀ {d} → Terms₁ d d
MIDS₁ {zero}  = ∙
MIDS₁ {suc d} = MLIFTS₁ MIDS₁


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


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop
    □_   : Prop → Prop


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop

infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop

Truths : Nat → Set
Truths g = Vec Truth g

Validities : Nat → Set
Validities d = Vec Validity d


record Derivation (d : Nat) : Set
  where
    constructor [_⊢_⦂_]
    field
      {g} : Nat
      Γ   : Truths g
      M   : Term d g
      Aₜ  : Truth


infix 3 _⋙_
data _⋙_ : ∀ {d} → Validities d → Derivation d → Set
  where
    var : ∀ {A d g i} → {Δ : Validities d} {Γ : Truths g}
                      → Γ ∋⟨ i ⟩ A true
                      → Δ ⋙ [ Γ ⊢ VAR i ⦂ A true ]

    lam : ∀ {A B d g M} → {Δ : Validities d} {Γ : Truths g}
                        → Δ ⋙ [ Γ , A true ⊢ M ⦂ B true ]
                        → Δ ⋙ [ Γ ⊢ LAM M ⦂ A ⊃ B true ]

    app : ∀ {A B d g M N} → {Δ : Validities d} {Γ : Truths g}
                          → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ] → Δ ⋙ [ Γ ⊢ N ⦂ A true ]
                          → Δ ⋙ [ Γ ⊢ APP M N ⦂ B true ]

    mvar : ∀ {A d g i} → {Δ : Validities d} {Γ : Truths g}
                       → Δ ∋⟨ i ⟩ A valid
                       → Δ ⋙ [ Γ ⊢ MVAR i ⦂ A true ]

    box : ∀ {A d g M} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⋙ [ ∙ ⊢ M ⦂ A true ]
                      → Δ ⋙ [ Γ ⊢ BOX M ⦂ □ A true ]

    letbox : ∀ {A B d g M N} → {Δ : Validities d} {Γ : Truths g}
                             → Δ ⋙ [ Γ ⊢ M ⦂ □ A true ] → Δ , A valid ⋙ [ Γ ⊢ N ⦂ B true ]
                             → Δ ⋙ [ Γ ⊢ LETBOX M N ⦂ B true ]


ren : ∀ {d g g′ e M A} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                       → Δ ⋙ [ Γ′ ⊢ REN e M ⦂ A true ]
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

wk : ∀ {B d g M A} → {Δ : Validities d} {Γ : Truths g}
                   → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                   → Δ ⋙ [ Γ , B true ⊢ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟

vz : ∀ {d g A} → {Δ : Validities d} {Γ : Truths g}
               → Δ ⋙ [ Γ , A true ⊢ VZ ⦂ A true ]
vz = var zero


mren : ∀ {d d′ g e M A} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths g}
                        → Δ′ ⊇⟨ e ⟩ Δ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                        → Δ′ ⋙ [ Γ ⊢ MREN e M ⦂ A true ]
mren η (var 𝒾)      = var 𝒾
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar 𝒾)     = mvar (ren∋ η 𝒾)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)

mwk : ∀ {B d g M A} → {Δ : Validities d} {Γ : Truths g}
                    → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                    → Δ , B valid ⋙ [ Γ ⊢ MWK M ⦂ A true ]
mwk 𝒟 = mren (drop id⊇) 𝒟

mvz : ∀ {d g A} → {Δ : Validities d} {Γ : Truths g}
                → Δ , A valid ⋙ [ Γ ⊢ MVZ ⦂ A true ]
mvz = mvar zero


record Derivations (d : Nat) : Set
  where
    constructor [_⊢⋆_⦂_]
    field
      {g} : Nat
      {x} : Nat
      Γ   : Truths g
      ζ   : Terms d g x
      Ξ   : Truths x


zap : ∀ {d g x} → Truths g → Terms d g x → Truths x
                → Vec (Derivation d) x
zap Γ ∙       ∙            = ∙
zap Γ (ζ , M) (Ξ , A true) = zap Γ ζ Ξ , [ Γ ⊢ M ⦂ A true ]

zap∋ : ∀ {d g x i A} → {Γ : Truths g}
                        {ζ : Terms d g x} {Ξ : Truths x}
                     → Ξ ∋⟨ i ⟩ A true
                     → zap Γ ζ Ξ ∋⟨ i ⟩ [ Γ ⊢ get ζ i ⦂ A true ]
zap∋ {ζ = ζ , M} {Ξ , A true} zero    = zero
zap∋ {ζ = ζ , N} {Ξ , B true} (suc 𝒾) = suc (zap∋ 𝒾)


infix 3 _⋙⋆_
_⋙⋆_ : ∀ {d} → Validities d → Derivations d → Set
Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] = All (Δ ⋙_) (zap Γ ζ Ξ)


rens : ∀ {d g g′ e x} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
                         {ζ : Terms d g x} {Ξ : Truths x}
                      → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                      → Δ ⋙⋆ [ Γ′ ⊢⋆ RENS e ζ ⦂ Ξ ]
rens {ζ = ∙}     {∙}          η ∙       = ∙
rens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = mapAll (ren η) ξ

wks : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
                     {ζ : Terms d g x} {Ξ : Truths x}
                  → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                  → Δ ⋙⋆ [ Γ , A true ⊢⋆ WKS ζ ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ

lifts : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
                       {ζ : Terms d g x} {Ξ : Truths x}
                    → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                    → Δ ⋙⋆ [ Γ , A true ⊢⋆ LIFTS ζ ⦂ Ξ , A true ]
lifts ξ = wks ξ , vz

ids : ∀ {d g} → {Δ : Validities d} {Γ : Truths g}
              → Δ ⋙⋆ [ Γ ⊢⋆ IDS ⦂ Γ ]
ids {Γ = ∙}          = ∙
ids {Γ = Γ , A true} = lifts ids


mrens : ∀ {d d′ g e x} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths g}
                          {ζ : Terms d g x} {Ξ : Truths x}
                       → Δ′ ⊇⟨ e ⟩ Δ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                       → Δ′ ⋙⋆ [ Γ ⊢⋆ MRENS e ζ ⦂ Ξ ]
mrens {ζ = ∙}     {∙}          η ∙       = ∙
mrens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = mrens η ξ , mren η 𝒟
-- NOTE: Equivalent to
-- mrens η ξ = mapAll (mren η) ξ

mwks : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
                      {ζ : Terms d g x} {Ξ : Truths x}
                   → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                   → Δ , A valid ⋙⋆ [ Γ ⊢⋆ MWKS ζ ⦂ Ξ ]
mwks ξ = mrens (drop id⊇) ξ


sub : ∀ {d g x M A} → {Δ : Validities d} {Γ : Truths g}
                       {ζ : Terms d g x} {Ξ : Truths x}
                    → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] → Δ ⋙ [ Ξ ⊢ M ⦂ A true ]
                    → Δ ⋙ [ Γ ⊢ SUB ζ M ⦂ A true ]
sub ξ (var 𝒾)      = lookup ξ (zap∋ 𝒾)
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar 𝒾)     = mvar 𝒾
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

cut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⋙ [ Γ ⊢ M ⦂ A true ] → Δ ⋙ [ Γ , A true ⊢ N ⦂ B true ]
                      → Δ ⋙ [ Γ ⊢ CUT M N ⦂ B true ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


record Derivation₁ (d : Nat) : Set
  where
    constructor [∙⊢₁_⦂_]
    field
      M  : Term₁ d
      Aᵥ : Validity

record Derivations₁ (d : Nat) : Set
  where
    constructor [∙⊢⋆₁_⦂_]
    field
      {x} : Nat
      ζ   : Terms₁ d x
      Ξ   : Validities x


zap₁ : ∀ {d x} → Terms₁ d x → Validities x
               → Vec (Derivation₁ d) x
zap₁ ∙       ∙             = ∙
zap₁ (ζ , M) (Ξ , A valid) = zap₁ ζ Ξ , [∙⊢₁ M ⦂ A valid ]

zap∋₁ : ∀ {d x i A} → {ζ : Terms₁ d x} {Ξ : Validities x}
                    → Ξ ∋⟨ i ⟩ A valid
                    → zap₁ ζ Ξ ∋⟨ i ⟩ [∙⊢₁ get ζ i ⦂ A valid ]
zap∋₁ {ζ = ζ , M} {Ξ , A valid} zero    = zero
zap∋₁ {ζ = ζ , N} {Ξ , B valid} (suc 𝒾) = suc (zap∋₁ 𝒾)


infix 3 _⋙₁_
_⋙₁_ : ∀ {d} → Validities d → Derivation₁ d → Set
Δ ⋙₁ [∙⊢₁ M ⦂ A valid ] = Δ ⋙ [ ∙ ⊢ M ⦂ A true ]

infix 3 _⋙⋆₁_
_⋙⋆₁_ : ∀ {d} → Validities d → Derivations₁ d → Set
Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] = All (Δ ⋙₁_) (zap₁ ζ Ξ)


mrens₁ : ∀ {d d′ e x} → {Δ : Validities d} {Δ′ : Validities d′} {ζ : Terms₁ d x} {Ξ : Validities x}
                      → Δ′ ⊇⟨ e ⟩ Δ → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                      → Δ′ ⋙⋆₁ [∙⊢⋆₁ MRENS₁ e ζ ⦂ Ξ ]
mrens₁ {ζ = ∙}     {∙}           η ∙       = ∙
mrens₁ {ζ = ζ , M} {Ξ , A valid} η (ξ , 𝒟) = mrens₁ η ξ , mren η 𝒟
-- NOTE: Equivalent to
-- mrens₁ η ξ = mapAll (mren η) ξ

mwks₁ : ∀ {d x A} → {Δ : Validities d} {ζ : Terms₁ d x} {Ξ : Validities x}
                  → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                  → Δ , A valid ⋙⋆₁ [∙⊢⋆₁ MWKS₁ ζ ⦂ Ξ ]
mwks₁ ξ = mrens₁ (drop id⊇) ξ

mlifts₁ : ∀ {d x A} → {Δ : Validities d} {ζ : Terms₁ d x} {Ξ : Validities x}
                    → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                    → Δ , A valid ⋙⋆₁ [∙⊢⋆₁ MLIFTS₁ ζ ⦂ Ξ , A valid ]
mlifts₁ ξ = mwks₁ ξ , mvz

mids₁ : ∀ {d} → {Δ : Validities d}
              → Δ ⋙⋆₁ [∙⊢⋆₁ MIDS₁ ⦂ Δ ]
mids₁ {Δ = ∙}           = ∙
mids₁ {Δ = Δ , A valid} = mlifts₁ mids₁


msub : ∀ {d g x M A} → {Δ : Validities d} {Γ : Truths g}
                        {ζ : Terms₁ d x} {Ξ : Validities x}
                     → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] → Ξ ⋙ [ Γ ⊢ M ⦂ A true ]
                     → Δ ⋙ [ Γ ⊢ MSUB ζ M ⦂ A true ]
msub ξ (var 𝒾)      = var 𝒾
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar 𝒾)     = sub ∙ (lookup ξ (zap∋₁ 𝒾))
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

mcut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
                       → Δ ⋙₁ [∙⊢₁ M ⦂ A valid ] → Δ , A valid ⋙ [ Γ ⊢ N ⦂ B true ]
                       → Δ ⋙ [ Γ ⊢ MCUT M N ⦂ B true ]
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


unlam : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ]
                      → Δ ⋙ [ Γ , A true ⊢ UNLAM M ⦂ B true ]
unlam 𝒟 = app (wk 𝒟) vz

shl : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                    → Δ ⋙ [ Γ , □ A true ⊢ M ⦂ B true ]
                    → Δ , A valid ⋙ [ Γ ⊢ SHL M ⦂ B true ]
shl 𝒟 = app (lam (mwk 𝒟)) (box mvz)

shr : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                    → Δ , A valid ⋙ [ Γ ⊢ M ⦂ B true ]
                    → Δ ⋙ [ Γ , □ A true ⊢ SHR M ⦂ B true ]
shr 𝒟 = letbox vz (wk 𝒟)

ex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
                     → Δ ⋙ [ Γ , A true , B true ⊢ M ⦂ C true ]
                     → Δ ⋙ [ Γ , B true , A true ⊢ EX M ⦂ C true ]
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)

mex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
                      → Δ , A valid , B valid ⋙ [ Γ ⊢ M ⦂ C true ]
                      → Δ , B valid , A valid ⋙ [ Γ ⊢ MEX M ⦂ C true ]
mex 𝒟 = shl (shl (ex (shr (shr 𝒟))))
