-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.

module BasicIS4.Syntax.DyadicGentzen where

open import BasicIS4.Syntax.Common public


-- Derivations.

infix 3 _⊢_
data _⊢_ : Cx² Ty Ty → Ty → Set where
  var   : ∀ {A Γ Δ}   → A ∈ Γ → Γ ⁏ Δ ⊢ A
  lam   : ∀ {A B Γ Δ} → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ▻ B
  app   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
  mvar  : ∀ {A Γ Δ}   → A ∈ Δ → Γ ⁏ Δ ⊢ A
  box   : ∀ {A Γ Δ}   → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A
  unbox : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ , A ⊢ C → Γ ⁏ Δ ⊢ C
  pair  : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ∧ B
  fst   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ A
  snd   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ B
  tt    : ∀ {Γ Δ}     → Γ ⁏ Δ ⊢ ⊤

infix 3 _⊢⋆_
_⊢⋆_ : Cx² Ty Ty → Cx Ty → Set
Γ ⁏ Δ ⊢⋆ ∅     = 𝟙
Γ ⁏ Δ ⊢⋆ Ξ , A = Γ ⁏ Δ ⊢⋆ Ξ × Γ ⁏ Δ ⊢ A


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ ⊢ A
mono⊢ η (var i)     = var (mono∈ η i)
mono⊢ η (lam t)     = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)   = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (mvar i)    = mvar i
mono⊢ η (box t)     = box t
mono⊢ η (unbox t u) = unbox (mono⊢ η t) (mono⊢ η u)
mono⊢ η (pair t u)  = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)     = fst (mono⊢ η t)
mono⊢ η (snd t)     = snd (mono⊢ η t)
mono⊢ η tt          = tt

mono⊢⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ′ ⁏ Δ ⊢⋆ Ξ
mono⊢⋆ {∅}     η ∙        = ∙
mono⊢⋆ {Ξ , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Monotonicity with respect to modal context inclusion.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
mmono⊢ θ (var i)     = var i
mmono⊢ θ (lam t)     = lam (mmono⊢ θ t)
mmono⊢ θ (app t u)   = app (mmono⊢ θ t) (mmono⊢ θ u)
mmono⊢ θ (mvar i)    = mvar (mono∈ θ i)
mmono⊢ θ (box t)     = box (mmono⊢ θ t)
mmono⊢ θ (unbox t u) = unbox (mmono⊢ θ t) (mmono⊢ (keep θ) u)
mmono⊢ θ (pair t u)  = pair (mmono⊢ θ t) (mmono⊢ θ u)
mmono⊢ θ (fst t)     = fst (mmono⊢ θ t)
mmono⊢ θ (snd t)     = snd (mmono⊢ θ t)
mmono⊢ θ tt          = tt

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

refl⊢⋆₀ : ∀ {Γ} → Γ ⁏ ∅ ⊢⋆ Γ
refl⊢⋆₀ {∅}     = ∙
refl⊢⋆₀ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆₀ , v₀

refl⊢⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆ = mmono⊢⋆ bot⊆ refl⊢⋆₀

mrefl⊢⋆₀ : ∀ {Δ} → ∅ ⁏ Δ ⊢⋆ □⋆ Δ
mrefl⊢⋆₀ {∅}     = ∙
mrefl⊢⋆₀ {Δ , A} = mmono⊢⋆ weak⊆ mrefl⊢⋆₀ , box mv₀

mrefl⊢⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Δ
mrefl⊢⋆ = mono⊢⋆ bot⊆ mrefl⊢⋆₀

mrefl⊢⋆′ : ∀ {Δ Δ′ Γ Γ′} → (∀ {A} → Γ ⁏ Δ ⊢ □ A → Γ′ ⁏ Δ′ ⊢ A) → Γ′ ⁏ Δ′ ⊢⋆ Δ
mrefl⊢⋆′ {∅}     f = ∙
mrefl⊢⋆′ {Δ , B} f = mrefl⊢⋆′ (f ∘ mmono⊢ weak⊆) , f (box mv₀)


-- Deduction theorem is built-in.

lam⋆ : ∀ {Ξ A Γ Δ} → Γ ⧺ Ξ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ Ξ ▻⋯▻ A
lam⋆ {∅}     = I
lam⋆ {Ξ , B} = lam⋆ {Ξ} ∘ lam

lam⋆₀ : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → ∅ ⁏ Δ ⊢ Γ ▻⋯▻ A
lam⋆₀ {∅}     = I
lam⋆₀ {Γ , B} = lam⋆₀ ∘ lam


-- Modal deduction theorem.

mlam : ∀ {A B Γ Δ} → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ ⊢ □ A ▻ B
mlam t = lam (unbox v₀ (mono⊢ weak⊆ t))

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

multicut² : ∀ {Ξ Ξ′ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ □⋆ Ξ′ → Ξ ⁏ Ξ′ ⊢ A → Γ ⁏ Δ ⊢ A
multicut² {∅}     ∙        us v = mmulticut us (mono⊢ bot⊆ v)
multicut² {Ξ , B} (ts , t) us v = app (multicut² ts us (lam v)) t


-- Tansitivity.

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
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app mv₁ mv₀)))

up : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ □ A
up t = unbox t (box (box mv₀))

down : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ A
down t = unbox t mv₀

distup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▻ B) → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B
distup t u = dist t (up u)


-- Useful theorems in combinatory form.

ci : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A ▻ A
ci = lam v₀

ck : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B ▻ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ▻ B) ▻ □ A ▻ □ B
cdist = lam (lam (dist v₁ v₀))

cup : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A ▻ □ □ A
cup = lam (up v₀)

cdown : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A ▻ A
cdown = lam (down v₀)

cdistup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▻ B) ▻ □ A ▻ □ B
cdistup = lam (lam (dist v₁ (up v₀)))

cunbox : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ □ A ▻ (□ A ▻ C) ▻ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B ▻ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▻ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▻ B
csnd = lam (snd v₀)


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
mpair t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (pair mv₁ mv₀)))

mfst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ∧ B) → Γ ⁏ Δ ⊢ □ A
mfst t = unbox t (box (fst mv₀))

msnd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ∧ B) → Γ ⁏ Δ ⊢ □ B
msnd t = unbox t (box (snd mv₀))


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ {Δ} → Γ , A ⁏ Δ ⊢ B → Γ′ ⁏ Δ ⊢ A → Γ ⧺ Γ′ ⁏ Δ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺₁ Γ′) (lam t)) (mono⊢ weak⊆⧺₂ u)

mconcat : ∀ {A B Γ Δ} Δ′ → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ′ ⊢ □ A → Γ ⁏ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺₁ Δ′) (mlam t)) (mmono⊢ weak⊆⧺₂ u)


-- Substitution.

[_≔_]_ : ∀ {A B Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ∖ i ⁏ Δ ⊢ B
[ i ≔ s ] var j     with i ≟∈ j
[ i ≔ s ] var .i    | same   = s
[ i ≔ s ] var ._    | diff j = var j
[ i ≔ s ] lam t     = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
[ i ≔ s ] app t u   = app ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] mvar j    = mvar j
[ i ≔ s ] box t     = box t
[ i ≔ s ] unbox t u = unbox ([ i ≔ s ] t) ([ i ≔ mmono⊢ weak⊆ s ] u)
[ i ≔ s ] pair t u  = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] fst t     = fst ([ i ≔ s ] t)
[ i ≔ s ] snd t     = snd ([ i ≔ s ] t)
[ i ≔ s ] tt        = tt

[_≔_]⋆_ : ∀ {Ξ A Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ∖ i ⁏ Δ ⊢⋆ Ξ
[_≔_]⋆_ {∅}     i s ∙        = ∙
[_≔_]⋆_ {Ξ , B} i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t


-- Modal substitution.

m[_≔_]_ : ∀ {A B Γ Δ} → (i : A ∈ Δ) → ∅ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ∖ i ⊢ B
m[ i ≔ s ] var j     = var j
m[ i ≔ s ] lam t     = lam (m[ i ≔ s ] t)
m[ i ≔ s ] app t u   = app (m[ i ≔ s ] t) (m[ i ≔ s ] u)
m[ i ≔ s ] mvar j    with i ≟∈ j
m[ i ≔ s ] mvar .i   | same   = mono⊢ bot⊆ s
m[ i ≔ s ] mvar ._   | diff j = mvar j
m[ i ≔ s ] box t     = box (m[ i ≔ s ] t)
m[ i ≔ s ] unbox t u = unbox (m[ i ≔ s ] t) (m[ pop i ≔ mmono⊢ weak⊆ s ] u)
m[ i ≔ s ] pair t u  = pair (m[ i ≔ s ] t) (m[ i ≔ s ] u)
m[ i ≔ s ] fst t     = fst (m[ i ≔ s ] t)
m[ i ≔ s ] snd t     = snd (m[ i ≔ s ] t)
m[ i ≔ s ] tt        = tt

m[_≔_]⋆_ : ∀ {Ξ A Γ Δ} → (i : A ∈ Δ) → ∅ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ∖ i ⊢⋆ Ξ
m[_≔_]⋆_ {∅}     i s ∙        = ∙
m[_≔_]⋆_ {Ξ , B} i s (ts , t) = m[ i ≔ s ]⋆ ts , m[ i ≔ s ] t


-- Conversion.

data _⋙_ {Γ Δ : Cx Ty} : ∀ {A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A → Set where
  refl⋙      : ∀ {A} {t : Γ ⁏ Δ ⊢ A}
                → t ⋙ t
  trans⋙     : ∀ {A} {t t′ t″ : Γ ⁏ Δ ⊢ A}
                → t ⋙ t′ → t′ ⋙ t″ → t ⋙ t″
  sym⋙       : ∀ {A} {t t′ : Γ ⁏ Δ ⊢ A}
                → t ⋙ t′ → t′ ⋙ t
  conglam⋙   : ∀ {A B} {t t′ : Γ , A ⁏ Δ ⊢ B}
                → t ⋙ t′
                → lam t ⋙ lam t′
  congapp⋙   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ▻ B} {u u′ : Γ ⁏ Δ ⊢ A}
                → t ⋙ t′ → u ⋙ u′
                → app t u ⋙ app t′ u′
  -- NOTE: Rejected by Pfenning and Davies.
  -- congbox⋙   : ∀ {A} {t t′ : ∅ ⁏ Δ ⊢ A}
  --               → t ⋙ t′
  --               → box {Γ} t ⋙ box {Γ} t′
  congunbox⋙ : ∀ {A C} {t t′ : Γ ⁏ Δ ⊢ □ A} {u u′ : Γ ⁏ Δ , A ⊢ C}
                → t ⋙ t′ → u ⋙ u′
                → unbox t u ⋙ unbox t′ u′
  congpair⋙  : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A} {u u′ : Γ ⁏ Δ ⊢ B}
                → t ⋙ t′ → u ⋙ u′
                → pair t u ⋙ pair t′ u′
  congfst⋙   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⋙ t′
                → fst t ⋙ fst t′
  congsnd⋙   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⋙ t′
                → snd t ⋙ snd t′
  beta▻⋙     : ∀ {A B} {t : Γ , A ⁏ Δ ⊢ B} {u : Γ ⁏ Δ ⊢ A}
                → app (lam t) u ⋙ ([ top ≔ u ] t)
  eta▻⋙      : ∀ {A B} {t : Γ ⁏ Δ ⊢ A ▻ B}
                → t ⋙ lam (app (mono⊢ weak⊆ t) v₀)
  -- TODO: Verify this.
  beta□⋙     : ∀ {A C} {t : ∅ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ , A ⊢ C}
                → unbox (box t) u ⋙ (m[ top ≔ t ] u)
  -- TODO: Verify this.
  eta□⋙      : ∀ {A} {t : Γ ⁏ Δ ⊢ □ A}
                → t ⋙ unbox t (box mv₀)
  -- TODO: What about commuting conversions for □?
  beta∧₁⋙    : ∀ {A B} {t : Γ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ ⊢ B}
                → fst (pair t u) ⋙ t
  beta∧₂⋙    : ∀ {A B} {t : Γ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ ⊢ B}
                → snd (pair t u) ⋙ u
  eta∧⋙      : ∀ {A B} {t : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⋙ pair (fst t) (snd t)
  eta⊤⋙     : ∀ {t : Γ ⁏ Δ ⊢ ⊤}
                → t ⋙ tt
