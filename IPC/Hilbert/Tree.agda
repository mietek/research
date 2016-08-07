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
  tt    : ⊢ ⊤
  cboom : ∀ {C}     → ⊢ ⊥ ▻ C
  cinl  : ∀ {A B}   → ⊢ A ▻ A ∨ B
  cinr  : ∀ {A B}   → ⊢ B ▻ A ∨ B
  ccase : ∀ {A B C} → ⊢ A ∨ B ▻ (A ▻ C) ▻ (B ▻ C) ▻ C

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
  cong⇒pair : ∀ {A B} {t t′ : ⊢ A} {u u′ : ⊢ B}
               → t ⇒ t′ → u ⇒ u′ → pair t u ⇒ pair t′ u′
  cong⇒fst  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′ → fst t ⇒ fst t′
  cong⇒snd  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′ → snd t ⇒ snd t′
  cong⇒boom : ∀ {C} {t t′ : ⊢ ⊥}
               → t ⇒ t′ → boom {C} t ⇒ boom t′
  cong⇒inl  : ∀ {A B} {t t′ : ⊢ A}
               → t ⇒ t′ → inl {A} {B} t ⇒ inl t′
  cong⇒inr  : ∀ {A B} {t t′ : ⊢ B}
               → t ⇒ t′ → inr {A} {B} t ⇒ inr t′
  cong⇒case : ∀ {A B C} {t t′ : ⊢ A ∨ B} {u u′ : ⊢ A ▻ C} {v v′ : ⊢ B ▻ C}
               → t ⇒ t′ → u ⇒ u′ → v ⇒ v′ → case t u v ⇒ case t′ u′ v′
  conv⇒k    : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → app (app ck t) u ⇒ t
  conv⇒s    : ∀ {A B C} {t : ⊢ A ▻ B ▻ C} {u : ⊢ A ▻ B} {v : ⊢ A}
               → app (app (app cs t) u) v ⇒ app (app t v) (app u v)
  conv⇒pair : ∀ {A B} {t : ⊢ A ∧ B}
               → t ⇒ pair (fst t) (snd t)
  conv⇒fst  : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → fst (pair t u) ⇒ t
  conv⇒snd  : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → snd (pair t u) ⇒ u
  conv⇒tt   : ∀ {t : ⊢ ⊤}
               → t ⇒ tt
  conv⇒inl  : ∀ {A B C} {t : ⊢ A} {u : ⊢ A ▻ C} {v : ⊢ B ▻ C}
               → case (inl t) u v ⇒ app u t
  conv⇒inr  : ∀ {A B C} {t : ⊢ B} {u : ⊢ A ▻ C} {v : ⊢ B ▻ C}
               → case (inr t) u v ⇒ app v t
