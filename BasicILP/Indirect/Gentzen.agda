module BasicILP.Indirect.Gentzen where

open import BasicILP.Indirect public


-- Derivations, as Gentzen-style natural deduction trees.

mutual
  data Tm : Set where
    VAR      : ℕ → Tm
    LAM      : Tm → Tm
    APP      : Tm → Tm → Tm
    MULTIBOX : Cx Tm → Tm → Tm
    DOWN     : Tm → Tm
    PAIR     : Tm → Tm → Tm
    FST      : Tm → Tm
    SND      : Tm → Tm
    TT       : Tm

  infix 3 _⊢_
  data _⊢_ (Γ : Cx (Ty Tm)) : Ty Tm → Set where
    var      : ∀ {A}   → A ∈ Γ → Γ ⊢ A
    lam      : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A ▷ B
    app      : ∀ {A B} → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
    multibox : ∀ {n A} {SS : VCx Tm n} {Π : VCx (Ty Tm) n}
               → Γ ⊢⋆ SS ⦂⋆ Π → (u : SS ⦂⋆ Π ⊢ A)
               → Γ ⊢ [ u ] ⦂ A
    down     : ∀ {A T} → Γ ⊢ T ⦂ A → Γ ⊢ A
    pair     : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
    fst      : ∀ {A B} → Γ ⊢ A ∧ B → Γ ⊢ A
    snd      : ∀ {A B} → Γ ⊢ A ∧ B → Γ ⊢ B
    tt       : Γ ⊢ ⊤

  infix 3 _⊢⋆_
  _⊢⋆_ : Cx (Ty Tm) → Cx (Ty Tm) → Set
  Γ ⊢⋆ ⌀     = Top
  Γ ⊢⋆ Π , A = Γ ⊢⋆ Π × Γ ⊢ A

  [_] : ∀ {A Γ} → Γ ⊢ A → Tm
  [ var i ]         = VAR [ i ]ᴵˣ
  [ lam t ]         = LAM [ t ]
  [ app t u ]       = APP [ t ] [ u ]
  [ multibox ts u ] = MULTIBOX [ ts ]⋆ [ u ]
  [ down t ]        = DOWN [ t ]
  [ pair t u ]      = PAIR [ t ] [ u ]
  [ fst t ]         = FST [ t ]
  [ snd t ]         = SND [ t ]
  [ tt ]            = TT

  [_]⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Cx Tm
  [_]⋆ {⌀}     ∙        = ⌀
  [_]⋆ {Π , A} (ts , t) = [ ts ]⋆ , [ t ]


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
  mono⊢ η (var i)         = var (mono∈ η i)
  mono⊢ η (lam t)         = lam (mono⊢ (keep η) t)
  mono⊢ η (app t u)       = app (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (multibox ts u) = multibox (mono⊢⋆ η ts) u
  mono⊢ η (down t)        = down (mono⊢ η t)
  mono⊢ η (pair t u)      = pair (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (fst t)         = fst (mono⊢ η t)
  mono⊢ η (snd t)         = snd (mono⊢ η t)
  mono⊢ η tt              = tt

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


-- Deduction theorem is built-in.

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
DIST T U = MULTIBOX ((⌀ , T) , U) (APP (DOWN V₁) (DOWN V₀))

UP : Tm → Tm
UP T = MULTIBOX (⌀ , T) V₀

DISTUP : Tm → Tm → Tm
DISTUP T U = DIST T (UP U)

BOX : Tm → Tm
BOX T = MULTIBOX ⌀ T

UNBOX : Tm → Tm → Tm
UNBOX T U = APP (LAM U) T

dist : ∀ {A B T U Γ}
       → (t : Γ ⊢ T ⦂ (A ▷ B)) → (u : Γ ⊢ U ⦂ A)
       → Γ ⊢ APP (DOWN V₁) (DOWN V₀) ⦂ B
dist t u = multibox ((∙ , t) , u) (app (down v₁) (down v₀))

up : ∀ {A T Γ}
     → Γ ⊢ T ⦂ A
     → Γ ⊢ V₀ ⦂ T ⦂ A
up t = multibox (∙ , t) v₀

distup : ∀ {A B T U Γ}
         → (t : Γ ⊢ T ⦂ (U ⦂ A ▷ B)) → (u : Γ ⊢ U ⦂ A)
         → Γ ⊢ APP (DOWN V₁) (DOWN V₀) ⦂ B
distup t u = dist t (up u)

box : ∀ {A Γ}
      → (t : ⌀ ⊢ A)
      → Γ ⊢ [ t ] ⦂ A
box t = multibox ∙ t

unbox : ∀ {A C T U Γ}
        → Γ ⊢ T ⦂ A → Γ , T ⦂ A ⊢ U ⦂ C
        → Γ ⊢ U ⦂ C
unbox t u = app (lam u) t


-- Useful theorems in combinatory form.

CI : Tm
CI = LAM V₀

CK : Tm
CK = LAM (LAM V₁)

CS : Tm
CS = LAM (LAM (LAM (APP (APP V₂ V₀) (APP V₁ V₀))))

CDIST : Tm
CDIST = LAM (LAM (DIST V₁ V₀))

CUP : Tm
CUP = LAM (UP V₀)

CDOWN : Tm
CDOWN = LAM (DOWN V₀)

CDISTUP : Tm
CDISTUP = LAM (LAM (DIST V₁ (UP V₀)))

CUNBOX : Tm
CUNBOX = LAM (LAM (APP V₀ V₁))

CPAIR : Tm
CPAIR = LAM (LAM (PAIR V₁ V₀))

CFST : Tm
CFST = LAM (FST V₀)

CSND : Tm
CSND = LAM (SND V₀)

ci : ∀ {A Γ} → Γ ⊢ A ▷ A
ci = lam v₀

ck : ∀ {A B Γ} → Γ ⊢ A ▷ B ▷ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {A B T U Γ}
        → Γ ⊢ T ⦂ (A ▷ B) ▷ U ⦂ A ▷ APP (DOWN V₁) (DOWN V₀) ⦂ B
cdist = lam (lam (dist v₁ v₀))

cup : ∀ {A T Γ} → Γ ⊢ T ⦂ A ▷ V₀ ⦂ T ⦂ A
cup = lam (up v₀)

cdown : ∀ {A T Γ} → Γ ⊢ T ⦂ A ▷ A
cdown = lam (down v₀)

cdistup : ∀ {A B T U Γ}
          → Γ ⊢ T ⦂ (U ⦂ A ▷ B) ▷ U ⦂ A ▷ APP (DOWN V₁) (DOWN V₀) ⦂ B
cdistup = lam (lam (dist v₁ (up v₀)))

cunbox : ∀ {A C T Γ} → Γ ⊢ T ⦂ A ▷ (T ⦂ A ▷ C) ▷ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {A B Γ} → Γ ⊢ A ▷ B ▷ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ} → Γ ⊢ A ∧ B ▷ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ} → Γ ⊢ A ∧ B ▷ B
csnd = lam (snd v₀)


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)


-- Substitution.

mutual
  [_≔_]_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢ B → Γ - i ⊢ B
  [ i ≔ s ] var j         with i ≟∈ j
  [ i ≔ s ] var .i        | same   = s
  [ i ≔ s ] var ._        | diff j = var j
  [ i ≔ s ] lam t         = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
  [ i ≔ s ] app t u       = app ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] multibox ts u = multibox ([ i ≔ s ]⋆ ts) u
  [ i ≔ s ] down t        = down ([ i ≔ s ] t)
  [ i ≔ s ] pair t u      = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] fst t         = fst ([ i ≔ s ] t)
  [ i ≔ s ] snd t         = snd ([ i ≔ s ] t)
  [ i ≔ s ] tt            = tt

  [_≔_]⋆_ : ∀ {Π A Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢⋆ Π → Γ - i ⊢⋆ Π
  [_≔_]⋆_ {⌀}     i s ∙        = ∙
  [_≔_]⋆_ {Π , B} i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t
