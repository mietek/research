module IPC.Hilbert.Tree where

open import IPC public


-- Derivations, as Hilbert-style trees of combinators, with context.

infix 3 ⊢_
data ⊢_ : Ty → Set where
  app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
  ci    : ∀ {A}     → ⊢ A ▻ A
  ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
  cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
  cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
  csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
  unit  : ⊢ ⊤
  cboom : ∀ {C}     → ⊢ ⊥ ▻ C
  cinl  : ∀ {A B}   → ⊢ A ▻ A ∨ B
  cinr  : ∀ {A B}   → ⊢ B ▻ A ∨ B
  ccase : ∀ {A B C} → ⊢ A ∨ B ▻ (A ▻ C) ▻ (B ▻ C) ▻ C

infix 3 ⊢⋆_
⊢⋆_ : Cx Ty → Set
⊢⋆ ∅     = 𝟙
⊢⋆ Ξ , A = ⊢⋆ Ξ × ⊢ A


-- Cut and multicut.

cut : ∀ {A B} → ⊢ A → ⊢ A ▻ B → ⊢ B
cut t u = app u t

multicut : ∀ {Ξ A} → ⊢⋆ Ξ → ⊢ Ξ ▻⋯▻ A → ⊢ A
multicut {∅}     ∙        u = u
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

boom : ∀ {C} → ⊢ ⊥ → ⊢ C
boom t = app cboom t

inl : ∀ {A B} → ⊢ A → ⊢ A ∨ B
inl t = app cinl t

inr : ∀ {A B} → ⊢ B → ⊢ A ∨ B
inr t = app cinr t

case : ∀ {A B C} → ⊢ A ∨ B → ⊢ A ▻ C → ⊢ B ▻ C → ⊢ C
case t u v = app (app (app ccase t) u) v


-- Convertibility.

data _⋙_ : ∀ {A} → ⊢ A → ⊢ A → Set where
  refl⋙     : ∀ {A} → {t : ⊢ A}
                     → t ⋙ t

  trans⋙    : ∀ {A} → {t t′ t″ : ⊢ A}
                     → t ⋙ t′ → t′ ⋙ t″
                     → t ⋙ t″

  sym⋙      : ∀ {A} → {t t′ : ⊢ A}
                     → t ⋙ t′
                     → t′ ⋙ t

  congapp⋙  : ∀ {A B} → {t t′ : ⊢ A ▻ B} → {u u′ : ⊢ A}
                       → t ⋙ t′ → u ⋙ u′
                       → app t u ⋙ app t′ u′

  congpair⋙ : ∀ {A B} → {t t′ : ⊢ A} → {u u′ : ⊢ B}
                       → t ⋙ t′ → u ⋙ u′
                       → app (app cpair t) u ⋙ app (app cpair t′) u′

  congi⋙    : ∀ {A} → {t t′ : ⊢ A}
                     → t ⋙ t′
                     → app ci t ⋙ app ci t′

  congk⋙    : ∀ {A B} → {t t′ : ⊢ A} → {u u′ : ⊢ B}
                       → t ⋙ t′ → u ⋙ u′
                       → app (app ck t) u ⋙ app (app ck t′) u′

  congs⋙    : ∀ {A B C} → {t t′ : ⊢ A ▻ B ▻ C} → {u u′ : ⊢ A ▻ B} → {v v′ : ⊢ A}
                         → t ⋙ t′ → u ⋙ u′ → v ⋙ v′
                         → app (app (app cs t) u) v ⋙ app (app (app cs t′) u′) v′

  congfst⋙  : ∀ {A B} → {t t′ : ⊢ A ∧ B}
                       → t ⋙ t′
                       → app cfst t ⋙ app cfst t′

  congsnd⋙  : ∀ {A B} → {t t′ : ⊢ A ∧ B}
                       → t ⋙ t′
                       → app csnd t ⋙ app csnd t′

  congboom⋙ : ∀ {C} → {t t′ : ⊢ ⊥}
                     → t ⋙ t′
                     → app (cboom {C = C}) t ⋙ app cboom t′

  conginl⋙  : ∀ {A B} → {t t′ : ⊢ A}
                       → t ⋙ t′
                       → app (cinl {A = A} {B}) t ⋙ app cinl t′

  conginr⋙  : ∀ {A B} → {t t′ : ⊢ B}
                       → t ⋙ t′
                       → app (cinr {A = A} {B}) t ⋙ app cinr t′

  congcase⋙ : ∀ {A B C} → {t t′ : ⊢ A ∨ B} → {u u′ : ⊢ A ▻ C} → {v v′ : ⊢ B ▻ C}
                         → t ⋙ t′ → u ⋙ u′ → v ⋙ v′
                         → app (app (app ccase t) u) v ⋙ app (app (app ccase t′) u′) v′

  -- TODO: Verify this.
  beta▻ₖ⋙   : ∀ {A B} → {t : ⊢ A} → {u : ⊢ B}
                       → app (app ck t) u ⋙ t

  -- TODO: Verify this.
  beta▻ₛ⋙   : ∀ {A B C} → {t : ⊢ A ▻ B ▻ C} → {u : ⊢ A ▻ B} → {v : ⊢ A}
                         → app (app (app cs t) u) v ⋙ app (app t v) (app u v)

  -- TODO: What about eta for ▻?
  beta∧₁⋙   : ∀ {A B} → {t : ⊢ A} → {u : ⊢ B}
                       → app cfst (app (app cpair t) u) ⋙ t

  beta∧₂⋙   : ∀ {A B} → {t : ⊢ A} → {u : ⊢ B}
                       → app csnd (app (app cpair t) u) ⋙ u

  eta∧⋙     : ∀ {A B} → {t : ⊢ A ∧ B}
                       → t ⋙ app (app cpair (app cfst t)) (app csnd t)

  eta⊤⋙    : ∀ {t : ⊢ ⊤} → t ⋙ unit

  -- TODO: Verify this.
  beta∨₁⋙   : ∀ {A B C} → {t : ⊢ A} → {u : ⊢ A ▻ C} → {v : ⊢ B ▻ C}
                         → app (app (app ccase (app cinl t)) u) v ⋙ app u t

  -- TODO: Verify this.
  beta∨₂⋙   : ∀ {A B C} → {t : ⊢ B} → {u : ⊢ A ▻ C} → {v : ⊢ B ▻ C}
                         → app (app (app ccase (app cinr t)) u) v ⋙ app v t

  -- TODO: What about eta and commuting conversions for ∨? What about ⊥?
