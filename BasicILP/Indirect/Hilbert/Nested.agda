module BasicILP.Indirect.Hilbert.Nested where

open import BasicILP.Indirect public


-- Derivations, as Hilbert-style combinator trees.

mutual
  data Tm : Set where
    VAR   : ℕ → Tm
    APP   : Tm → Tm → Tm
    CI    : Tm
    CK    : Tm
    CS    : Tm
    BOX   : Tm → Tm
    CDIST : Tm
    CUP   : Tm
    CDOWN : Tm
    CPAIR : Tm
    CFST  : Tm
    CSND  : Tm
    TT    : Tm

  infix 3 _⊢_
  data _⊢_ (Γ : Cx (Ty Tm)) : Ty Tm → Set where
    var   : ∀ {A}           → A ∈ Γ → Γ ⊢ A
    app   : ∀ {A B}         → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
    ci    : ∀ {A}           → Γ ⊢ A ▷ A
    ck    : ∀ {A B}         → Γ ⊢ A ▷ B ▷ A
    cs    : ∀ {A B C}       → Γ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
    box   : ∀ {A}           → (t : ⌀ ⊢ A) → Γ ⊢ [ t ] ⦂ A
    cdist : ∀ {A B [t] [u]} → Γ ⊢ [t] ⦂ (A ▷ B) ▷ [u] ⦂ A ▷ APP [t] [u] ⦂ B
    cup   : ∀ {A [t]}       → Γ ⊢ [t] ⦂ A ▷ BOX [t] ⦂ [t] ⦂ A
    cdown : ∀ {A [t]}       → Γ ⊢ [t] ⦂ A ▷ A
    cpair : ∀ {A B}         → Γ ⊢ A ▷ B ▷ A ∧ B
    cfst  : ∀ {A B}         → Γ ⊢ A ∧ B ▷ A
    csnd  : ∀ {A B}         → Γ ⊢ A ∧ B ▷ B
    tt    : Γ ⊢ ⊤

  [_] : ∀ {A Γ} → Γ ⊢ A → Tm
  [ var i ]   = VAR (ix i)
  [ app t u ] = APP [ t ] [ u ]
  [ ci ]      = CI
  [ ck ]      = CK
  [ cs ]      = CS
  [ box t ]   = BOX [ t ]
  [ cdist ]   = CDIST
  [ cup ]     = CUP
  [ cdown ]   = CDOWN
  [ cpair ]   = CPAIR
  [ cfst ]    = CFST
  [ csnd ]    = CSND
  [ tt ]      = TT

infix 3 _⊢⋆_
_⊢⋆_ : Cx (Ty Tm) → Cx (Ty Tm) → Set
Γ ⊢⋆ ⌀     = Top
Γ ⊢⋆ Π , A = Γ ⊢⋆ Π × Γ ⊢ A


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η (box t)   = box t
mono⊢ η cdist     = cdist
mono⊢ η cup       = cup
mono⊢ η cdown     = cdown
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η tt        = tt

mono⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Π → Γ′ ⊢⋆ Π
mono⊢⋆ {⌀}     η ∙        = ∙
mono⊢⋆ {Π , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Shorthand for variables.

V₀ : Tm
V₀ = VAR 0

V₁ : Tm
V₁ = VAR 1

V₂ : Tm
V₂ = VAR 2

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → (Γ , A) , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → ((Γ , A) , B) , C ⊢ A
v₂ = var i₂


-- Deduction theorem.

LAM : Tm → Tm
LAM (VAR zero)    = CI
LAM (VAR (suc i)) = APP CK (VAR i)
LAM (APP [t] [u]) = APP (APP CS (LAM [t])) (LAM [u])
LAM CI            = APP CK CI
LAM CK            = APP CK CK
LAM CS            = APP CK CS
LAM (BOX [t])     = APP CK (BOX [t])
LAM CDIST         = APP CK CDIST
LAM CUP           = APP CK CUP
LAM CDOWN         = APP CK CDOWN
LAM CPAIR         = APP CK CPAIR
LAM CFST          = APP CK CFST
LAM CSND          = APP CK CSND
LAM TT            = APP CK TT

lam : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ▷ B
lam (var top)     = ci
lam (var (pop i)) = app ck (var i)
lam (app t u)     = app (app cs (lam t)) (lam u)
lam ci            = app ck ci
lam ck            = app ck ck
lam cs            = app ck cs
lam (box t)       = app ck (box t)
lam cdist         = app ck cdist
lam cup           = app ck cup
lam cdown         = app ck cdown
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd
lam tt            = app ck tt


-- Detachment theorem.

DET : Tm → Tm
DET [t] = APP [t] V₀

det : ∀ {A B Γ} → Γ ⊢ A ▷ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Additional useful properties.

MULTICUT : Cx Tm → Tm → Tm
MULTICUT ⌀            [u] = [u]
MULTICUT ([ts] , [t]) [u] = APP (MULTICUT [ts] (LAM [u])) [t]

multicut⊢ : ∀ {A Γ Γ′} → Γ ⊢⋆ Γ′ → Γ′ ⊢ A → Γ ⊢ A
multicut⊢ {Γ′ = ⌀}      ∙        u = mono⊢ bot⊆ u
multicut⊢ {Γ′ = Γ′ , B} (ts , t) u = app (multicut⊢ ts (lam u)) t

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {⌀}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

trans⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Π → Γ ⊢⋆ Π
trans⊢⋆ {⌀}     ts ∙        = ∙
trans⊢⋆ {Π , A} ts (us , u) = trans⊢⋆ ts us , multicut⊢ ts u


-- Contraction.

CCONT : Tm
CCONT = LAM (LAM (APP (APP V₁ V₀) V₀))

CONT : Tm → Tm
CONT [t] = DET (APP CCONT (LAM (LAM [t])))

ccont : ∀ {A B Γ} → Γ ⊢ (A ▷ A ▷ B) ▷ A ▷ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → (Γ , A) , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

CEXCH : Tm
CEXCH = LAM (LAM (LAM (APP (APP V₂ V₀) V₁)))

EXCH : Tm → Tm
EXCH [t] = DET (DET (APP CEXCH (LAM (LAM [t]))))

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ B ▷ A ▷ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → (Γ , A) , B ⊢ C → (Γ , B) , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

CCOMP : Tm
CCOMP = LAM (LAM (LAM (APP V₂ (APP V₁ V₀))))

COMP : Tm → Tm → Tm
COMP [t] [u] = DET (APP (APP CCOMP (LAM [t])) (LAM [u]))

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

DIST : Tm → Tm → Tm
DIST [t] [u] = APP (APP CDIST [t]) [u]

UP : Tm → Tm
UP [t] = APP CUP [t]

DOWN : Tm → Tm
DOWN [t] = APP CDOWN [t]

DISTUP : Tm → Tm → Tm
DISTUP [t] [u] = DIST [t] (UP [u])

UNBOX : Tm → Tm → Tm
UNBOX [t] [u] = APP (LAM [u]) [t]

MULTIBOX : Cx Tm → Tm → Tm
MULTIBOX ⌀            [u] = BOX [u]
MULTIBOX ([ts] , [t]) [u] = DISTUP (MULTIBOX [ts] (LAM [u])) [t]

dist : ∀ {A B [t] [u] Γ}
       → Γ ⊢ [t] ⦂ (A ▷ B) → Γ ⊢ [u] ⦂ A
       → Γ ⊢ (APP [t] [u]) ⦂ B
dist t u = app (app cdist t) u

up : ∀ {A [t] Γ}
     → Γ ⊢ [t] ⦂ A
     → Γ ⊢ BOX [t] ⦂ [t] ⦂ A
up t = app cup t

down : ∀ {A [t] Γ}
       → Γ ⊢ [t] ⦂ A
       → Γ ⊢ A
down t = app cdown t

distup : ∀ {A B [t] [u] Γ}
         → Γ ⊢ [t] ⦂ ([u] ⦂ A ▷ B) → Γ ⊢ [u] ⦂ A
         → Γ ⊢ APP [t] (BOX [u]) ⦂ B
distup t u = dist t (up u)

unbox : ∀ {A C [t] [u] Γ}
        → Γ ⊢ [t] ⦂ A → Γ , [t] ⦂ A ⊢ [u] ⦂ C
        → Γ ⊢ [u] ⦂ C
unbox t u = app (lam u) t


-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- Do we need reduction on term representations?
--
-- Goal: Γ ⊢ [ u ] ⦂ A
-- Have: Γ ⊢ APP [ lam u ] (BOX [s]) ⦂ A

distup′ : ∀ {A B [t] [u] Γ} → Γ ⊢ LAM [t] ⦂ ([u] ⦂ A ▷ B) → Γ ⊢ [u] ⦂ A
          → Γ ⊢ APP (LAM [t]) (BOX [u]) ⦂ B
distup′ t u = dist t (up u)

-- multibox : ∀ {n A Γ} {[ss] : VCx Tm n} {Π : VCx (Ty Tm) n}
--            → Γ ⊢⋆ [ss] ⦂⋆ Π → (u : [ss] ⦂⋆ Π ⊢ A)
--            → Γ ⊢ [ u ] ⦂ A
-- multibox {[ss] = ⌀}          {⌀}     ∙        u = box u
-- multibox {[ss] = [ss] , [s]} {Π , B} (ts , t) u = {!distup (multibox ts (lam u)) t!}

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


PAIR : Tm → Tm → Tm
PAIR [t] [u] = APP (APP CPAIR [t]) [u]

FST : Tm → Tm
FST [t] = APP CFST [t]

SND : Tm → Tm
SND [t] = APP CSND [t]

pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
snd t = app csnd t


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)
