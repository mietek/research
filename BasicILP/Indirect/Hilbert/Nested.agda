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
    var   : ∀ {A}       → A ∈ Γ → Γ ⊢ A
    app   : ∀ {A B}     → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
    ci    : ∀ {A}       → Γ ⊢ A ▷ A
    ck    : ∀ {A B}     → Γ ⊢ A ▷ B ▷ A
    cs    : ∀ {A B C}   → Γ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
    box   : ∀ {A}       → (t : ⌀ ⊢ A) → Γ ⊢ [ t ] ⦂ A
    cdist : ∀ {A B T U} → Γ ⊢ T ⦂ (A ▷ B) ▷ U ⦂ A ▷ APP T U ⦂ B
    cup   : ∀ {A T}     → Γ ⊢ T ⦂ A ▷ BOX T ⦂ T ⦂ A
    cdown : ∀ {A T}     → Γ ⊢ T ⦂ A ▷ A
    cpair : ∀ {A B}     → Γ ⊢ A ▷ B ▷ A ∧ B
    cfst  : ∀ {A B}     → Γ ⊢ A ∧ B ▷ A
    csnd  : ∀ {A B}     → Γ ⊢ A ∧ B ▷ B
    tt    : Γ ⊢ ⊤

  [_] : ∀ {A Γ} → Γ ⊢ A → Tm
  [ var i ]   = VAR [ i ]ᴵˣ
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
LAM (APP T U)     = APP (APP CS (LAM T)) (LAM U)
LAM CI            = APP CK CI
LAM CK            = APP CK CK
LAM CS            = APP CK CS
LAM (BOX T)       = APP CK (BOX T)
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
DET T = APP T V₀

det : ∀ {A B Γ} → Γ ⊢ A ▷ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Cut and multicut.

CUT : Tm → Tm → Tm
CUT T U = APP (LAM U) T

MULTICUT : Cx Tm → Tm → Tm
MULTICUT ⌀        U = U
MULTICUT (TS , T) U = APP (MULTICUT TS (LAM U)) T

cut : ∀ {A B Γ} → Γ ⊢ A → ⌀ , A ⊢ B → Γ ⊢ B
cut t u = app (mono⊢ bot⊆ (lam u)) t

multicut : ∀ {Π A Γ} → Γ ⊢⋆ Π → Π ⊢ A → Γ ⊢ A
multicut {⌀}     ∙        u = mono⊢ bot⊆ u
multicut {Π , B} (ts , t) u = app (multicut ts (lam u)) t


-- Reflexivity and transitivity.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {⌀}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

trans⊢⋆ : ∀ {Γ″ Γ′ Γ} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Γ″ → Γ ⊢⋆ Γ″
trans⊢⋆ {⌀}      ts ∙        = ∙
trans⊢⋆ {Γ″ , A} ts (us , u) = trans⊢⋆ ts us , multicut ts u


-- Contraction.

CCONT : Tm
CCONT = LAM (LAM (APP (APP V₁ V₀) V₀))

CONT : Tm → Tm
CONT T = DET (APP CCONT (LAM (LAM T)))

ccont : ∀ {A B Γ} → Γ ⊢ (A ▷ A ▷ B) ▷ A ▷ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → (Γ , A) , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

CEXCH : Tm
CEXCH = LAM (LAM (LAM (APP (APP V₂ V₀) V₁)))

EXCH : Tm → Tm
EXCH T = DET (DET (APP CEXCH (LAM (LAM T))))

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ B ▷ A ▷ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → (Γ , A) , B ⊢ C → (Γ , B) , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

CCOMP : Tm
CCOMP = LAM (LAM (LAM (APP V₂ (APP V₁ V₀))))

COMP : Tm → Tm → Tm
COMP T U = DET (APP (APP CCOMP (LAM T)) (LAM U))

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

DIST : Tm → Tm → Tm
DIST T U = APP (APP CDIST T) U

UP : Tm → Tm
UP T = APP CUP T

DOWN : Tm → Tm
DOWN T = APP CDOWN T

DISTUP : Tm → Tm → Tm
DISTUP T U = DIST T (UP U)

UNBOX : Tm → Tm → Tm
UNBOX T U = APP (LAM U) T

MULTIBOX : Cx Tm → Tm → Tm
MULTIBOX ⌀        U = BOX U
MULTIBOX (TS , T) U = DISTUP (MULTIBOX TS (LAM U)) T

dist : ∀ {A B T U Γ} → Γ ⊢ T ⦂ (A ▷ B) → Γ ⊢ U ⦂ A → Γ ⊢ (APP T U) ⦂ B
dist t u = app (app cdist t) u

up : ∀ {A T Γ} → Γ ⊢ T ⦂ A → Γ ⊢ BOX T ⦂ T ⦂ A
up t = app cup t

down : ∀ {A T Γ} → Γ ⊢ T ⦂ A → Γ ⊢ A
down t = app cdown t

distup : ∀ {A B T U Γ} → Γ ⊢ T ⦂ (U ⦂ A ▷ B)
         → Γ ⊢ U ⦂ A → Γ ⊢ APP T (BOX U) ⦂ B
distup t u = dist t (up u)

unbox : ∀ {A C T U Γ} → Γ ⊢ T ⦂ A → Γ , T ⦂ A ⊢ U ⦂ C → Γ ⊢ U ⦂ C
unbox t u = app (lam u) t


-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- Do we need reduction on term representations?
--
-- Goal: Γ ⊢ [ u ] ⦂ A
-- Have: Γ ⊢ APP [ lam u ] (BOX S) ⦂ A

distup′ : ∀ {A B T U Γ} → Γ ⊢ LAM T ⦂ (U ⦂ A ▷ B) → Γ ⊢ U ⦂ A
          → Γ ⊢ APP (LAM T) (BOX U) ⦂ B
distup′ t u = dist t (up u)

-- multibox : ∀ {n A Γ} {SS : VCx Tm n} {Π : VCx (Ty Tm) n}
--            → Γ ⊢⋆ SS ⦂⋆ Π → (u : SS ⦂⋆ Π ⊢ A)
--            → Γ ⊢ [ u ] ⦂ A
-- multibox {SS = ⌀}      {⌀}     ∙        u = box u
-- multibox {SS = SS , S} {Π , B} (ts , t) u = {!distup (multibox ts (lam u)) t!}

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


PAIR : Tm → Tm → Tm
PAIR T U = APP (APP CPAIR T) U

FST : Tm → Tm
FST T = APP CFST T

SND : Tm → Tm
SND T = APP CSND T

pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
snd t = app csnd t


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)
