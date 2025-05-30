{-# OPTIONS --sized-types #-}

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Hilbert-style formalisation of syntax with context pairs.
-- Nested terms.

module A201607.BasicIS4.Syntax.DyadicHilbert where

open import A201607.BasicIS4.Syntax.Common public


-- Derivations.

infix 3 _⊢_
data _⊢_ : Cx² Ty Ty → Ty → Set where
  var   : ∀ {A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ ⊢ A
  app   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
  ci    : ∀ {A Γ Δ}     → Γ ⁏ Δ ⊢ A ▻ A
  ck    : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ▻ B ▻ A
  cs    : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  mvar  : ∀ {A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ ⊢ A
  box   : ∀ {A Γ Δ}     → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A
  cdist : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {A Γ Δ}     → Γ ⁏ Δ ⊢ □ A ▻ □ □ A
  cdown : ∀ {A Γ Δ}     → Γ ⁏ Δ ⊢ □ A ▻ A
  cpair : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ▻ B ▻ A ∧ B
  cfst  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ∧ B ▻ A
  csnd  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ∧ B ▻ B
  unit  : ∀ {Γ Δ}       → Γ ⁏ Δ ⊢ ⊤

infix 3 _⊢⋆_
_⊢⋆_ : Cx² Ty Ty → Cx Ty → Set
Γ ⁏ Δ ⊢⋆ ∅     = 𝟙
Γ ⁏ Δ ⊢⋆ Ξ , A = Γ ⁏ Δ ⊢⋆ Ξ × Γ ⁏ Δ ⊢ A


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η (mvar i)  = mvar i
mono⊢ η (box t)   = box t
mono⊢ η cdist     = cdist
mono⊢ η cup       = cup
mono⊢ η cdown     = cdown
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η unit      = unit

mono⊢⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ′ ⁏ Δ ⊢⋆ Ξ
mono⊢⋆ {∅}     η ∙        = ∙
mono⊢⋆ {Ξ , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Monotonicity with respect to modal context inclusion.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
mmono⊢ θ (var i)   = var i
mmono⊢ θ (app t u) = app (mmono⊢ θ t) (mmono⊢ θ u)
mmono⊢ θ ci        = ci
mmono⊢ θ ck        = ck
mmono⊢ θ cs        = cs
mmono⊢ θ (mvar i)  = mvar (mono∈ θ i)
mmono⊢ θ (box t)   = box (mmono⊢ θ t)
mmono⊢ θ cdist     = cdist
mmono⊢ θ cup       = cup
mmono⊢ θ cdown     = cdown
mmono⊢ θ cpair     = cpair
mmono⊢ θ cfst      = cfst
mmono⊢ θ csnd      = csnd
mmono⊢ θ unit      = unit

mmono⊢⋆ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ′ ⊢⋆ Ξ
mmono⊢⋆ {∅}     θ ∙        = ∙
mmono⊢⋆ {Ξ , A} θ (ts , t) = mmono⊢⋆ θ ts , mmono⊢ θ t


-- Monotonicity using context pairs.

mono²⊢ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ A → Π′ ⊢ A
mono²⊢ (η , θ) = mono⊢ η ∘ mmono⊢ θ


-- Shorthand for variables.

v₀ : ∀ {A Γ Δ} → Γ , A ⁏ Δ ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → Γ , A , B ⁏ Δ ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → Γ , A , B , C ⁏ Δ ⊢ A
v₂ = var i₂

mv₀ : ∀ {A Γ Δ} → Γ ⁏ Δ , A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {A B Γ Δ} → Γ ⁏ Δ , A , B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {A B C Γ Δ} → Γ ⁏ Δ , A , B , C ⊢ A
mv₂ = mvar i₂


-- Reflexivity.

refl⊢⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

mrefl⊢⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ □⋆ Δ
mrefl⊢⋆ {∅}     = ∙
mrefl⊢⋆ {Δ , A} = mmono⊢⋆ weak⊆ mrefl⊢⋆ , box mv₀


-- Deduction theorem.

lam : ∀ {A B Γ Δ} → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ▻ B
lam (var top)     = ci
lam (var (pop i)) = app ck (var i)
lam (app t u)     = app (app cs (lam t)) (lam u)
lam ci            = app ck ci
lam ck            = app ck ck
lam cs            = app ck cs
lam (mvar i)      = app ck (mvar i)
lam (box t)       = app ck (box t)
lam cdist         = app ck cdist
lam cup           = app ck cup
lam cdown         = app ck cdown
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd
lam unit          = app ck unit

lam⋆ : ∀ {Ξ A Γ Δ} → Γ ⧺ Ξ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ Ξ ▻⋯▻ A
lam⋆ {∅}     = I
lam⋆ {Ξ , B} = lam⋆ {Ξ} ∘ lam

lam⋆₀ : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → ∅ ⁏ Δ ⊢ Γ ▻⋯▻ A
lam⋆₀ {∅}     = I
lam⋆₀ {Γ , B} = lam⋆₀ ∘ lam


-- Combined axioms of distribution and transitivity.

cdistup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▻ B) ▻ □ A ▻ □ B
cdistup = app (app cs (app (app cs (app ck cs))
                           (app (app cs (app (app cs (app ck cs))
                                             (lam (lam cdist))))
                                (app (app cs (app ck ck)) ci))))
              (app (app cs (app (app cs (app ck cs))
                                (lam (lam cup))))
                   (app ck ci))


-- Modal deduction theorem.

mlam : ∀ {A B Γ Δ} → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ ⊢ □ A ▻ B
mlam (var i)        = app ck (var i)
mlam (app t u)      = app (app cs (mlam t)) (mlam u)
mlam ci             = app ck ci
mlam ck             = app ck ck
mlam cs             = app ck cs
mlam (mvar top)     = cdown
mlam (mvar (pop i)) = app ck (mvar i)
mlam (box t)        = app cdistup (box (mlam t))
mlam cdist          = app ck cdist
mlam cup            = app ck cup
mlam cdown          = app ck cdown
mlam cpair          = app ck cpair
mlam cfst           = app ck cfst
mlam csnd           = app ck csnd
mlam unit           = app ck unit

mlam⋆ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⧺ Ξ ⊢ A → Γ ⁏ Δ ⊢ □⋆ Ξ ▻⋯▻ A
mlam⋆ {∅}     = I
mlam⋆ {Ξ , B} = mlam⋆ {Ξ} ∘ mlam

mlam⋆₀ : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ ∅ ⊢ □⋆ Δ ▻⋯▻ A
mlam⋆₀ {∅}     = I
mlam⋆₀ {Δ , B} = mlam⋆₀ ∘ mlam


-- Detachment theorems.

det : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ , A ⁏ Δ ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

det⋆ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢ Ξ ▻⋯▻ A → Γ ⧺ Ξ ⁏ Δ ⊢ A
det⋆ {∅}     = I
det⋆ {Ξ , B} = det ∘ det⋆ {Ξ}

det⋆₀ : ∀ {Γ A Δ} → ∅ ⁏ Δ ⊢ Γ ▻⋯▻ A → Γ ⁏ Δ ⊢ A
det⋆₀ {∅}     = I
det⋆₀ {Γ , B} = det ∘ det⋆₀

mdet : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ A ▻ B → Γ ⁏ Δ , A ⊢ B
mdet t = app (mmono⊢ weak⊆ t) (box mv₀)

mdet⋆ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢ □⋆ Ξ ▻⋯▻ A → Γ ⁏ Δ ⧺ Ξ ⊢ A
mdet⋆ {∅}     = I
mdet⋆ {Ξ , B} = mdet ∘ mdet⋆ {Ξ}

mdet⋆₀ : ∀ {Δ A Γ} → Γ ⁏ ∅ ⊢ □⋆ Δ ▻⋯▻ A → Γ ⁏ Δ ⊢ A
mdet⋆₀ {∅}     = I
mdet⋆₀ {Δ , B} = mdet ∘ mdet⋆₀


-- Context manipulation.

merge : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⧺ (□⋆ Δ) ⁏ ∅ ⊢ A
merge {Δ} = det⋆ {□⋆ Δ} ∘ mlam⋆₀

mmerge : ∀ {Γ A Δ} → □⋆ Γ ⁏ Δ ⊢ A → ∅ ⁏ Δ ⧺ Γ ⊢ A
mmerge {Γ} = mdet⋆ {Γ} ∘ lam⋆₀

split : ∀ {Δ A Γ} → Γ ⧺ (□⋆ Δ) ⁏ ∅ ⊢ A → Γ ⁏ Δ ⊢ A
split {Δ} = mdet⋆₀ ∘ lam⋆ {□⋆ Δ}

msplit : ∀ {Γ A Δ} → ∅ ⁏ Δ ⧺ Γ ⊢ A → □⋆ Γ ⁏ Δ ⊢ A
msplit {Γ} = det⋆₀ ∘ mlam⋆ {Γ}

merge⋆ : ∀ {Ξ Δ Γ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⧺ (□⋆ Δ) ⁏ ∅ ⊢⋆ Ξ
merge⋆ {∅}     ∙        = ∙
merge⋆ {Ξ , A} (ts , t) = merge⋆ ts , merge t

split⋆ : ∀ {Ξ Δ Γ} → Γ ⧺ (□⋆ Δ) ⁏ ∅ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
split⋆ {∅}     ∙        = ∙
split⋆ {Ξ , A} (ts , t) = split⋆ ts , split t


-- Cut and multicut.

cut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ B
cut t u = app (lam u) t

mcut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ ⊢ B
mcut t u = app (mlam u) t

multicut : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Ξ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
multicut {∅}     ∙        u = mono⊢ bot⊆ u
multicut {Ξ , B} (ts , t) u = app (multicut ts (lam u)) t

mmulticut : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Ξ → Γ ⁏ Ξ ⊢ A → Γ ⁏ Δ ⊢ A
mmulticut {∅}     ∙        u = mmono⊢ bot⊆ u
mmulticut {Ξ , B} (ts , t) u = app (mmulticut ts (mlam u)) t


-- Transitivity.

trans⊢⋆₀ : ∀ {Γ″ Γ′ Γ} → Γ ⁏ ∅ ⊢⋆ Γ′ → Γ′ ⁏ ∅ ⊢⋆ Γ″ → Γ ⁏ ∅ ⊢⋆ Γ″
trans⊢⋆₀ {∅}      ts ∙        = ∙
trans⊢⋆₀ {Γ″ , A} ts (us , u) = trans⊢⋆₀ ts us , multicut ts u

trans⊢⋆ : ∀ {Ξ Γ Γ′ Δ Δ′} → Γ ⁏ Δ ⊢⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
trans⊢⋆ ts us = split⋆ (trans⊢⋆₀ (merge⋆ ts) (merge⋆ us))


-- Contraction.

ccont : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ Δ} → Γ , A , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ B
cont t = det (app ccont (lam (lam t)))

mcont : ∀ {A B Γ Δ} → Γ ⁏ Δ , A , A ⊢ B → Γ ⁏ Δ , A ⊢ B
mcont t = mdet (app ccont (mlam (mlam t)))


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ Δ} → Γ , A , B ⁏ Δ ⊢ C → Γ , B , A ⁏ Δ ⊢ C
exch t = det (det (app cexch (lam (lam t))))

mexch : ∀ {A B C Γ Δ} → Γ ⁏ Δ , A , B ⊢ C → Γ ⁏ Δ , B , A ⊢ C
mexch t = mdet (mdet (app cexch (mlam (mlam t))))


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ Δ} → Γ , B ⁏ Δ ⊢ C → Γ , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))

mcomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ , B ⊢ □ C → Γ ⁏ Δ , A ⊢ □ B → Γ ⁏ Δ , A ⊢ □ C
mcomp t u = mdet (app (app ccomp (mlam t)) (mlam u))


-- Useful theorems in functional form.

dist : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ▻ B) → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B
dist t u = app (app cdist t) u

up : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ □ A
up t = app cup t

down : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ A
down t = app cdown t

distup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▻ B) → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B
distup t u = dist t (up u)

unbox : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ , A ⊢ C → Γ ⁏ Δ ⊢ C
unbox t u = app (mlam u) t

pair : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ B
snd t = app csnd t


-- Internalisation, or lifting, and additional theorems.

lift : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → □⋆ Γ ⁏ Δ ⊢ □ A
lift {∅}     t = box t
lift {Γ , B} t = det (app cdist (lift (lam t)))

hypup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ □ A ▻ B
hypup t = lam (app (mono⊢ weak⊆ t) (down v₀))

hypdown : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ □ A ▻ B → Γ ⁏ Δ ⊢ □ A ▻ B
hypdown t = lam (app (mono⊢ weak⊆ t) (up v₀))

cxup : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → □⋆ Γ ⁏ Δ ⊢ A
cxup {∅}     t = t
cxup {Γ , B} t = det (hypup (cxup (lam t)))

cxdown : ∀ {Γ A Δ} → □⋆ □⋆ Γ ⁏ Δ ⊢ A → □⋆ Γ ⁏ Δ ⊢ A
cxdown {∅}     t = t
cxdown {Γ , B} t = det (hypdown (cxdown (lam t)))

box⋆ : ∀ {Ξ Γ Δ} → ∅ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ □⋆ Ξ
box⋆ {∅}     ∙        = ∙
box⋆ {Ξ , A} (ts , t) = box⋆ ts , box t

lift⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → □⋆ Γ ⁏ Δ ⊢⋆ □⋆ Ξ
lift⋆ {∅}     ∙        = ∙
lift⋆ {Ξ , A} (ts , t) = lift⋆ ts , lift t

up⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Ξ → Γ ⁏ Δ ⊢⋆ □⋆ □⋆ Ξ
up⋆ {∅}     ∙        = ∙
up⋆ {Ξ , A} (ts , t) = up⋆ ts , up t

down⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
down⋆ {∅}     ∙        = ∙
down⋆ {Ξ , A} (ts , t) = down⋆ ts , down t

multibox : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Ξ → □⋆ Ξ ⁏ ∅ ⊢ A → Γ ⁏ Δ ⊢ □ A
multibox ts u = multicut (up⋆ ts) (mmono⊢ bot⊆ (lift u))

dist′ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ▻ B) → Γ ⁏ Δ ⊢ □ A ▻ □ B
dist′ t = lam (dist (mono⊢ weak⊆ t) v₀)

mpair : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B → Γ ⁏ Δ ⊢ □ (A ∧ B)
mpair t u = dist (dist (box cpair) t) u

mfst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ∧ B) → Γ ⁏ Δ ⊢ □ A
mfst t = dist (box cfst) t

msnd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ∧ B) → Γ ⁏ Δ ⊢ □ B
msnd t = dist (box csnd) t


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ {Δ} → Γ , A ⁏ Δ ⊢ B → Γ′ ⁏ Δ ⊢ A → Γ ⧺ Γ′ ⁏ Δ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺₁ Γ′) (lam t)) (mono⊢ weak⊆⧺₂ u)

mconcat : ∀ {A B Γ Δ} Δ′ → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ′ ⊢ □ A → Γ ⁏ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺₁ Δ′) (mlam t)) (mmono⊢ weak⊆⧺₂ u)


-- Convertibility.

data _⋙_ {Γ Δ : Cx Ty} : ∀ {A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A → Set where
  refl⋙     : ∀ {A} → {t : Γ ⁏ Δ ⊢ A}
                     → t ⋙ t

  trans⋙    : ∀ {A} → {t t′ t″ : Γ ⁏ Δ ⊢ A}
                     → t ⋙ t′ → t′ ⋙ t″
                     → t ⋙ t″

  sym⋙      : ∀ {A} → {t t′ : Γ ⁏ Δ ⊢ A}
                     → t ⋙ t′
                     → t′ ⋙ t

  congapp⋙  : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ▻ B} → {u u′ : Γ ⁏ Δ ⊢ A}
                       → t ⋙ t′ → u ⋙ u′
                       → app t u ⋙ app t′ u′

  congi⋙    : ∀ {A} → {t t′ : Γ ⁏ Δ ⊢ A}
                     → t ⋙ t′
                     → app ci t ⋙ app ci t′

  congk⋙    : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A} → {u u′ : Γ ⁏ Δ ⊢ B}
                       → t ⋙ t′ → u ⋙ u′
                       → app (app ck t) u ⋙ app (app ck t′) u′

  congs⋙    : ∀ {A B C} → {t t′ : Γ ⁏ Δ ⊢ A ▻ B ▻ C} → {u u′ : Γ ⁏ Δ ⊢ A ▻ B} → {v v′ : Γ ⁏ Δ ⊢ A}
                         → t ⋙ t′ → u ⋙ u′ → v ⋙ v′

  -- NOTE: Rejected by Pfenning and Davies.
  -- congbox⋙  : ∀ {A} → {t t′ : ∅ ⁏ Δ ⊢ A}
  --                    → t ⋙ t′
  --                    → box {Γ} t ⋙ box {Γ} t′

  congdist⋙ : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ □ (A ▻ B)} → {u u′ : Γ ⁏ Δ ⊢ □ A}
                       → t ⋙ t′ → u ⋙ u′
                       → app (app cdist t) u ⋙ app (app cdist t′) u′

  congup⋙   : ∀ {A} → {t t′ : Γ ⁏ Δ ⊢ □ A}
                     → t ⋙ t′
                     → app cup t ⋙ app cup t′

  congdown⋙ : ∀ {A} → {t t′ : Γ ⁏ Δ ⊢ □ A}
                     → t ⋙ t′
                     → app cdown t ⋙ app cdown t′

  congpair⋙ : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A} → {u u′ : Γ ⁏ Δ ⊢ B}
                       → t ⋙ t′ → u ⋙ u′
                       → app (app cpair t) u ⋙ app (app cpair t′) u′

  congfst⋙  : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                       → t ⋙ t′
                       → app cfst t ⋙ app cfst t′

  congsnd⋙  : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                       → t ⋙ t′
                       → app csnd t ⋙ app csnd t′

  -- TODO: Verify this.
  beta▻ₖ⋙   : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ ⊢ B}
                       → app (app ck t) u ⋙ t

  -- TODO: Verify this.
  beta▻ₛ⋙   : ∀ {A B C} → {t : Γ ⁏ Δ ⊢ A ▻ B ▻ C} → {u : Γ ⁏ Δ ⊢ A ▻ B} → {v : Γ ⁏ Δ ⊢ A}
                         → app (app (app cs t) u) v ⋙ app (app t v) (app u v)

  -- TODO: What about eta for ▻? What about beta, eta, and commuting conversions for □?

  beta∧₁⋙   : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ ⊢ B}
                       → app cfst (app (app cpair t) u) ⋙ t

  beta∧₂⋙   : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ ⊢ B}
                       → app csnd (app (app cpair t) u) ⋙ u

  eta∧⋙     : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A ∧ B}
                       → t ⋙ app (app cpair (app cfst t)) (app csnd t)

  eta⊤⋙    : ∀ {t : Γ ⁏ Δ ⊢ ⊤} → t ⋙ unit
