module NewBasicILP.UntypedSyntax.ClosedHilbert where

open import NewBasicILP.UntypedSyntax.Common public


-- Untyped representation of derivations.

data Rep : Set where
  APP   : Rep → Rep → Rep
  CI    : Rep
  CK    : Rep
  CS    : Rep
  BOX   : Rep → Rep
  CDIST : Rep
  CUP   : Rep
  CDOWN : Rep
  CPAIR : Rep
  CFST  : Rep
  CSND  : Rep
  TT    : Rep

open ClosedSyntax (Rep) public


-- Derivations.

mutual
  infix 3 ⊢_
  data ⊢_ : Ty → Set where
    app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
    ci    : ∀ {A}     → ⊢ A ▻ A
    ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
    cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    box   : ∀ {A}     → (p : ⊢ A)
                      → ⊢ [ REP p ] A

    cdist : ∀ {A B}   → ∀ {p q}
                      → ⊢ [ p ] (A ▻ B) ▻ [ q ] A ▻ [ APP p q ] B

    cup   : ∀ {A}     → ∀ {p}
                      → ⊢ [ p ] A ▻ [ BOX p ] [ p ] A

    cdown : ∀ {A}     → ∀ {p}
                      → ⊢ [ p ] A ▻ A

    cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
    cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
    csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
    tt    : ⊢ ⊤

  REP : ∀ {A} → ⊢ A → Rep
  REP (app t u) = APP (REP t) (REP u)
  REP ci        = CI
  REP ck        = CK
  REP cs        = CS
  REP (box p)   = BOX (REP p)
  REP cdist     = CDIST
  REP cup       = CUP
  REP cdown     = CDOWN
  REP cpair     = CPAIR
  REP cfst      = CFST
  REP csnd      = CSND
  REP tt        = TT

infix 3 ⊢⋆_
⊢⋆_ : Cx Ty → Set
⊢⋆ ⌀     = 𝟙
⊢⋆ Ξ , A = ⊢⋆ Ξ × ⊢ A


-- Cut and multicut.

cut : ∀ {A B} → ⊢ A → ⊢ A ▻ B → ⊢ B
cut t u = app u t

multicut : ∀ {Ξ A} → ⊢⋆ Ξ → ⊢ Ξ ▻⋯▻ A → ⊢ A
multicut {⌀}     ∙        u = u
multicut {Ξ , B} (ts , t) u = app (multicut ts u) t


-- Contraction.

ccont : ∀ {A B} → ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = app (app cs cs) (app ck ci)

cont : ∀ {A B} → ⊢ A ▻ A ▻ B → ⊢ A ▻ B
cont t = app ccont t


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = app (app cs (app (app cs (app ck cs))
                         (app (app cs (app ck ck)) cs)))
            (app ck ck)

exch : ∀ {A B C} → ⊢ A ▻ B ▻ C → ⊢ B ▻ A ▻ C
exch t = app cexch t


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C} → ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = app (app cs (app ck cs)) ck

comp : ∀ {A B C} → ⊢ B ▻ C → ⊢ A ▻ B → ⊢ A ▻ C
comp t u = app (app ccomp t) u


-- Useful theorems in functional form.

pair : ∀ {A B} → ⊢ A → ⊢ B → ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B} → ⊢ A ∧ B → ⊢ A
fst t = app cfst t

snd : ∀ {A B} → ⊢ A ∧ B → ⊢ B
snd t = app csnd t
