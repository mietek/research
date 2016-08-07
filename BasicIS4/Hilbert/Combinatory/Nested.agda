module BasicIS4.Hilbert.Combinatory.Nested where

open import BasicIS4 public


-- Derivations, as context-free Hilbert-style combinator trees.

infix 3 ⊢_
data ⊢_ : Ty → Set where
  app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
  ci    : ∀ {A}     → ⊢ A ▻ A
  ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
  cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  box   : ∀ {A}     → ⊢ A → ⊢ □ A
  cdist : ∀ {A B}   → ⊢ □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {A}     → ⊢ □ A ▻ □ □ A
  cdown : ∀ {A}     → ⊢ □ A ▻ A
  cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
  cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
  csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
  tt    : ⊢ ⊤

infix 3 ⊢⋆_
⊢⋆_ : Cx Ty → Set
⊢⋆ ⌀     = 𝟙
⊢⋆ Π , A = ⊢⋆ Π × ⊢ A


-- Cut and multicut.

cut : ∀ {A B} → ⊢ A → ⊢ A ▻ B → ⊢ B
cut t u = app u t

multicut : ∀ {Π A} → ⊢⋆ Π → ⊢ Π ▻⋯▻ A → ⊢ A
multicut {⌀}     ∙        u = u
multicut {Π , B} (ts , t) u = app (multicut ts u) t


-- Contraction.

ccont : ∀ {A B} → ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = app (app cs cs) (app ck ci)

cont : ∀ {A B} → ⊢ A ▻ A ▻ B → ⊢ A ▻ B
cont t = app ccont t


-- Exchange.

-- NOTE: This seems to be the normal form.
cexch : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = app
         (app cs
          (app (app cs (app ck cs))
           (app
            (app cs
             (app (app cs (app ck cs)) (app (app cs (app ck ck)) (app ck cs))))
            (app
             (app cs
              (app (app cs (app ck cs))
               (app
                (app cs
                 (app (app cs (app ck cs)) (app (app cs (app ck ck)) (app ck cs))))
                (app
                 (app cs
                  (app (app cs (app ck cs)) (app (app cs (app ck ck)) (app ck ck))))
                 (app (app cs (app ck ck)) ci)))))
             (app (app cs (app ck ck)) (app ck ci))))))
         (app
          (app cs
           (app (app cs (app ck cs)) (app (app cs (app ck ck)) (app ck ck))))
          (app ck ci))

exch : ∀ {A B C} → ⊢ A ▻ B ▻ C → ⊢ B ▻ A ▻ C
exch t = app cexch t


-- Composition.

ccomp : ∀ {A B C} → ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = app (app cs (app ck cs)) ck

comp : ∀ {A B C} → ⊢ B ▻ C → ⊢ A ▻ B → ⊢ A ▻ C
comp t u = app (app ccomp t) u


-- Useful theorems in functional form.

dist : ∀ {A B} → ⊢ □ (A ▻ B) → ⊢ □ A → ⊢ □ B
dist t u = app (app cdist t) u

up : ∀ {A} → ⊢ □ A → ⊢ □ □ A
up t = app cup t

down : ∀ {A} → ⊢ □ A → ⊢ A
down t = app cdown t

distup : ∀ {A B} → ⊢ □ (□ A ▻ B) → ⊢ □ A → ⊢ □ B
distup t u = dist t (up u)

pair : ∀ {A B} → ⊢ A → ⊢ B → ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B} → ⊢ A ∧ B → ⊢ A
fst t = app cfst t

snd : ∀ {A B} → ⊢ A ∧ B → ⊢ B
snd t = app csnd t


-- Conversion.

data _⇒_ : ∀ {A} → ⊢ A → ⊢ A → Set where
  refl⇒     : ∀ {A} {t : ⊢ A}
               → t ⇒ t
  trans⇒    : ∀ {A} {t t′ t″ : ⊢ A}
               → t ⇒ t′ → t′ ⇒ t″ → t ⇒ t″
  sym⇒      : ∀ {A} {t t′ : ⊢ A}
               → t ⇒ t′ → t′ ⇒ t
  cong⇒app  : ∀ {A B} {t t′ : ⊢ A ▻ B} {u u′ : ⊢ A}
               → t ⇒ t′ → u ⇒ u′ → app t u ⇒ app t′ u′
  -- NOTE: Rejected by Pfenning and Davies.
  -- cong⇒box  : ∀ {A} {t t′ : ⊢ A}
  --              → t ⇒ t′ → box t ⇒ box t′
  cong⇒dist : ∀ {A B} {t t′ : ⊢ □ (A ▻ B)} {u u′ : ⊢ □ A}
               → t ⇒ t′ → u ⇒ u′ → dist t u ⇒ dist t′ u′
  cong⇒up   : ∀ {A} {t t′ : ⊢ □ A}
               → t ⇒ t′ → up t ⇒ up t′
  cong⇒down : ∀ {A} {t t′ : ⊢ □ A}
               → t ⇒ t′ → down t ⇒ down t′
  cong⇒pair : ∀ {A B} {t t′ : ⊢ A} {u u′ : ⊢ B}
               → t ⇒ t′ → u ⇒ u′ → pair t u ⇒ pair t′ u′
  cong⇒fst  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′ → fst t ⇒ fst t′
  cong⇒snd  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′ → snd t ⇒ snd t′
  conv⇒k    : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → app (app ck t) u ⇒ t
  conv⇒s    : ∀ {A B C} {t : ⊢ A ▻ B ▻ C} {u : ⊢ A ▻ B} {v : ⊢ A}
               → app (app (app cs t) u) v ⇒ app (app t v) (app u v)
  -- TODO: Verify this.
  conv⇒up   : ∀ {A} {t : ⊢ □ A}
               → down (up t) ⇒ t
  -- TODO: Verify this.
  conv⇒down : ∀ {A} {t : ⊢ A}
               → t ⇒ down (box t)
  conv⇒pair : ∀ {A B} {t : ⊢ A ∧ B}
               → t ⇒ pair (fst t) (snd t)
  conv⇒fst  : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → fst (pair t u) ⇒ t
  conv⇒snd  : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → snd (pair t u) ⇒ u
  conv⇒tt   : ∀ {t : ⊢ ⊤}
               → t ⇒ tt
