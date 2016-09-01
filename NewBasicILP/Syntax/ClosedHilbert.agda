-- Hilbert-style formalisation of closed syntax.
-- Nested terms.

module NewBasicILP.Syntax.ClosedHilbert where

open import NewBasicILP.Syntax.Common public


-- Types parametrised by closed derivations.

mutual
  infixr 9 _⦂_
  infixl 8 _∧_
  infixr 6 _▻_
  data Ty : Set where
    α_  : Atom → Ty
    _▻_ : Ty → Ty → Ty
    _⦂_ : ∀ {A} → Proof A → Ty → Ty
    _∧_ : Ty → Ty → Ty
    ⊤  : Ty


  -- Anti-bug wrappers.

  record Proof (A : Ty) : Set where
    inductive
    constructor [_]
    field
      der : ⊢ A


  -- Derivations.

  infix 3 ⊢_
  data ⊢_ : Ty → Set where
    app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
    ci    : ∀ {A}     → ⊢ A ▻ A
    ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
    cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    box   : ∀ {A}     → (d : ⊢ A)
                      → ⊢ [ d ] ⦂ A

    cdist : ∀ {A B}   → {d₁ : ⊢ A ▻ B} {d₂ : ⊢ A}
                      → ⊢ [ d₁ ] ⦂ (A ▻ B) ▻ [ d₂ ] ⦂ A ▻ [ app d₁ d₂ ] ⦂ B

    cup   : ∀ {A}     → {d : ⊢ A}
                      → ⊢ [ d ] ⦂ A ▻ [ box d ] ⦂ [ d ] ⦂ A

    cdown : ∀ {A}     → {d : ⊢ A}
                      → ⊢ [ d ] ⦂ A ▻ A

    cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
    cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
    csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
    tt    : ⊢ ⊤

infix 3 ⊢⋆_
⊢⋆_ : Cx Ty → Set
⊢⋆ ∅     = 𝟙
⊢⋆ Ξ , A = ⊢⋆ Ξ × ⊢ A


-- Additional useful types.

infixr 6 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
∅       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)


-- Cut and multicut.

cut : ∀ {A B} → ⊢ A → ⊢ A ▻ B → ⊢ B
cut d₁ d₂ = app d₂ d₁

multicut : ∀ {Ξ A} → ⊢⋆ Ξ → ⊢ Ξ ▻⋯▻ A → ⊢ A
multicut {∅}     ∙         d₂ = d₂
multicut {Ξ , B} (ds , d₁) d₂ = app (multicut ds d₂) d₁


-- Contraction.

ccont : ∀ {A B} → ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = app (app cs cs) (app ck ci)

cont : ∀ {A B} → ⊢ A ▻ A ▻ B → ⊢ A ▻ B
cont d = app ccont d


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = app (app cs (app (app cs (app ck cs))
                         (app (app cs (app ck ck)) cs)))
            (app ck ck)

exch : ∀ {A B C} → ⊢ A ▻ B ▻ C → ⊢ B ▻ A ▻ C
exch d = app cexch d


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C} → ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = app (app cs (app ck cs)) ck

comp : ∀ {A B C} → ⊢ B ▻ C → ⊢ A ▻ B → ⊢ A ▻ C
comp d₁ d₂ = app (app ccomp d₁) d₂


-- Useful theorems in functional form.

dist : ∀ {A B r₁ r₂} → ⊢ [ r₁ ] ⦂ (A ▻ B) → ⊢ [ r₂ ] ⦂ A → ⊢ [ app r₁ r₂ ] ⦂ B
dist d₁ d₂ = app (app cdist d₁) d₂

up : ∀ {A r} → ⊢ [ r ] ⦂ A → ⊢ [ box r ] ⦂ [ r ] ⦂ A
up d = app cup d

down : ∀ {A r} → ⊢ [ r ] ⦂ A → ⊢ A
down d = app cdown d

distup : ∀ {A B} → {r₀ : ⊢ A} {r₁ : ⊢ [ r₀ ] ⦂ A ▻ B}
         → ⊢ [ r₁ ] ⦂ ([ r₀ ] ⦂ A ▻ B) → ⊢ [ r₀ ] ⦂ A → ⊢ [ app r₁ (box r₀) ] ⦂ B
distup d₁ d₂ = dist d₁ (up d₂)

pair : ∀ {A B} → ⊢ A → ⊢ B → ⊢ A ∧ B
pair d₁ d₂ = app (app cpair d₁) d₂

fst : ∀ {A B} → ⊢ A ∧ B → ⊢ A
fst d = app cfst d

snd : ∀ {A B} → ⊢ A ∧ B → ⊢ B
snd d = app csnd d
