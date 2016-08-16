-- Hilbert-style axiomatic formalisation of closed syntax.

module New.BasicIPC.Syntax.ClosedHilbert where

open import New.BasicIPC.Syntax.Common public


-- Derivations.

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


-- Conversion.

data _⇒_ : ∀ {A} → ⊢ A → ⊢ A → Set where
  refl⇒     : ∀ {A} {t : ⊢ A}
               → t ⇒ t
  trans⇒    : ∀ {A} {t t′ t″ : ⊢ A}
               → t ⇒ t′ → t′ ⇒ t″ → t ⇒ t″
  sym⇒      : ∀ {A} {t t′ : ⊢ A}
               → t ⇒ t′ → t′ ⇒ t
  congapp⇒  : ∀ {A B} {t t′ : ⊢ A ▻ B} {u u′ : ⊢ A}
               → t ⇒ t′ → u ⇒ u′
               → app t u ⇒ app t′ u′
  congi⇒    : ∀ {A} {t t′ : ⊢ A}
               → t ⇒ t′
               → app ci t ⇒ app ci t′
  congk⇒    : ∀ {A B} {t t′ : ⊢ A} {u u′ : ⊢ B}
               → t ⇒ t′ → u ⇒ u′
               → app (app ck t) u ⇒ app (app ck t′) u′
  congs⇒    : ∀ {A B C} {t t′ : ⊢ A ▻ B ▻ C} {u u′ : ⊢ A ▻ B} {v v′ : ⊢ A}
               → t ⇒ t′ → u ⇒ u′ → v ⇒ v′
               → app (app (app cs t) u) v ⇒ app (app (app cs t′) u′) v′
  congpair⇒ : ∀ {A B} {t t′ : ⊢ A} {u u′ : ⊢ B}
               → t ⇒ t′ → u ⇒ u′
               → app (app cpair t) u ⇒ app (app cpair t′) u′
  congfst⇒  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′
               → app cfst t ⇒ app cfst t′
  congsnd⇒  : ∀ {A B} {t t′ : ⊢ A ∧ B}
               → t ⇒ t′
               → app csnd t ⇒ app csnd t′
  -- TODO: Verify this.
  beta▻ₖ⇒   : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → app (app ck t) u ⇒ t
  -- TODO: Verify this.
  beta▻ₛ⇒   : ∀ {A B C} {t : ⊢ A ▻ B ▻ C} {u : ⊢ A ▻ B} {v : ⊢ A}
               → app (app (app cs t) u) v ⇒ app (app t v) (app u v)
  -- TODO: What about eta for ▻?
  beta∧₁⇒   : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → app cfst (app (app cpair t) u) ⇒ t
  beta∧₂⇒   : ∀ {A B} {t : ⊢ A} {u : ⊢ B}
               → app csnd (app (app cpair t) u) ⇒ u
  eta∧⇒     : ∀ {A B} {t : ⊢ A ∧ B}
               → t ⇒ app (app cpair (app cfst t)) (app csnd t)
  eta⊤⇒    : ∀ {t : ⊢ ⊤}
               → t ⇒ tt
