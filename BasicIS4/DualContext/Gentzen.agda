module BasicIS4.DualContext.Gentzen where

open import BasicIS4 public


-- Derivations, as Gentzen-style natural deduction trees, following Pfenning and Davies.

infix 3 _⁏_⊢_
data _⁏_⊢_ (Γ Δ : Cx Ty) : Ty → Set where
  var   : ∀ {A}   → A ∈ Γ → Γ ⁏ Δ ⊢ A
  lam   : ∀ {A B} → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ▷ B
  app   : ∀ {A B} → Γ ⁏ Δ ⊢ A ▷ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
  mvar  : ∀ {A}   → A ∈ Δ → Γ ⁏ Δ ⊢ A
  box   : ∀ {A}   → ⌀ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A
  unbox : ∀ {A C} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ , A ⊢ C → Γ ⁏ Δ ⊢ C
  pair  : ∀ {A B} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ∧ B
  fst   : ∀ {A B} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ A
  snd   : ∀ {A B} → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ B
  tt    : Γ ⁏ Δ ⊢ ⊤

infix 3 _⁏_⊢⋆_
_⁏_⊢⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
Γ ⁏ Δ ⊢⋆ ⌀     = Top
Γ ⁏ Δ ⊢⋆ Π , A = Γ ⁏ Δ ⊢⋆ Π × Γ ⁏ Δ ⊢ A


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

mono⊢⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ Π → Γ′ ⁏ Δ ⊢⋆ Π
mono⊢⋆ {⌀}     η ∙        = ∙
mono⊢⋆ {Π , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Monotonicity with respect to modal context inclusion.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
mmono⊢ η (var i)     = var i
mmono⊢ η (lam t)     = lam (mmono⊢ η t)
mmono⊢ η (app t u)   = app (mmono⊢ η t) (mmono⊢ η u)
mmono⊢ η (mvar i)    = mvar (mono∈ η i)
mmono⊢ η (box t)     = box (mmono⊢ η t)
mmono⊢ η (unbox t u) = unbox (mmono⊢ η t) (mmono⊢ (keep η) u)
mmono⊢ η (pair t u)  = pair (mmono⊢ η t) (mmono⊢ η u)
mmono⊢ η (fst t)     = fst (mmono⊢ η t)
mmono⊢ η (snd t)     = snd (mmono⊢ η t)
mmono⊢ η tt          = tt

mmono⊢⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ′ ⊢⋆ Π
mmono⊢⋆ {⌀}     η ∙        = ∙
mmono⊢⋆ {Π , A} η (ts , t) = mmono⊢⋆ η ts , mmono⊢ η t


-- Shorthand for variables.

mv₀ : ∀ {A Γ Δ} → Γ ⁏ Δ , A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {A B Γ Δ} → Γ ⁏ (Δ , A) , B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {A B C Γ Δ} → Γ ⁏ ((Δ , A) , B) , C ⊢ A
mv₂ = mvar i₂

v₀ : ∀ {A Γ Δ} → Γ , A ⁏ Δ ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → (Γ , A) , B ⁏ Δ ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → ((Γ , A) , B) , C ⁏ Δ ⊢ A
v₂ = var i₂


-- Deduction theorem is built-in.

lam⋆ : ∀ {Π A Γ Δ} → Γ ⧺ Π ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ Π ▷⋯▷ A
lam⋆ {⌀}     t = t
lam⋆ {Π , B} t = lam⋆ {Π} (lam t)


-- Modal deduction theorem.

mlam : ∀ {A B Γ Δ} → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ ⊢ □ A ▷ B
mlam t = lam (unbox v₀ (mono⊢ weak⊆ t))

mlam⋆₀ : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ ⌀ ⊢ □⋆ Δ ▷⋯▷ A
mlam⋆₀ {⌀}     t = t
mlam⋆₀ {Δ , B} t = mlam⋆₀ (mlam t)


-- Detachment theorems.

det : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▷ B → Γ , A ⁏ Δ ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

det⋆ : ∀ {Π A Γ Δ} → Γ ⁏ Δ ⊢ Π ▷⋯▷ A → Γ ⧺ Π ⁏ Δ ⊢ A
det⋆ {⌀}     t = t
det⋆ {Π , A} t = det (det⋆ {Π} t)

mdet : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ A ▷ B → Γ ⁏ Δ , A ⊢ B
mdet t = app (mmono⊢ weak⊆ t) (box mv₀)

mdet⋆₀ : ∀ {Δ A Γ} → Γ ⁏ ⌀ ⊢ □⋆ Δ ▷⋯▷ A → Γ ⁏ Δ ⊢ A
mdet⋆₀ {⌀}     t = t
mdet⋆₀ {Δ , A} t = mdet (mdet⋆₀ t)


-- Dual context manipulation.

merge : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A
merge {Δ} t = det⋆ {□⋆ Δ} (mlam⋆₀ t)

split : ∀ {Δ A Γ} → Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A → Γ ⁏ Δ ⊢ A
split {Δ} t = mdet⋆₀ (lam⋆ {□⋆ Δ} t)

merge⋆ : ∀ {Π Δ Γ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢⋆ Π
merge⋆ {⌀}     ∙        = ∙
merge⋆ {Π , A} (ts , t) = merge⋆ ts , merge t

split⋆ : ∀ {Π Δ Γ} → Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢⋆ Π → Γ ⁏ Δ ⊢⋆ Π
split⋆ {⌀}     ∙        = ∙
split⋆ {Π , A} (ts , t) = split⋆ ts , split t


-- Cut and multicut.

cut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → ⌀ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ B
cut t u = app (mono⊢ bot⊆ (lam u)) t

mcut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ ⌀ , A ⊢ B → Γ ⁏ Δ ⊢ B
mcut t u = app (mmono⊢ bot⊆ (mlam u)) t

multicut : ∀ {Π A Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Π ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
multicut {⌀}     ∙        u = mono⊢ bot⊆ u
multicut {Π , B} (ts , t) u = app (multicut ts (lam u)) t

mmulticut : ∀ {Π A Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Π → Γ ⁏ Π ⊢ A → Γ ⁏ Δ ⊢ A
mmulticut {⌀}     ∙        u = mmono⊢ bot⊆ u
mmulticut {Π , B} (ts , t) u = app (mmulticut ts (mlam u)) t


-- Reflexivity and transitivity.

refl⊢⋆₀ : ∀ {Γ} → Γ ⁏ ⌀ ⊢⋆ Γ
refl⊢⋆₀ {⌀}     = ∙
refl⊢⋆₀ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆₀ , v₀

refl⊢⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ Γ ⧺ (□⋆ Δ)
refl⊢⋆ = split⋆ (merge⋆ refl⊢⋆₀)

trans⊢⋆₀ : ∀ {Γ″ Γ′ Γ} → Γ ⁏ ⌀ ⊢⋆ Γ′ → Γ′ ⁏ ⌀ ⊢⋆ Γ″ → Γ ⁏ ⌀ ⊢⋆ Γ″
trans⊢⋆₀ {⌀}      ts ∙        = ∙
trans⊢⋆₀ {Γ″ , A} ts (us , u) = trans⊢⋆₀ ts us , multicut ts u

trans⊢⋆ : ∀ {Π Γ Γ′ Δ Δ′} → Γ ⁏ Δ ⊢⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊢⋆ Π → Γ ⁏ Δ ⊢⋆ Π
trans⊢⋆ ts us = split⋆ (trans⊢⋆₀ (merge⋆ ts) (merge⋆ us))


-- Contraction.

ccont : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ (A ▷ A ▷ B) ▷ A ▷ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ Δ} → (Γ , A) , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ B
cont t = det (app ccont (lam (lam t)))

mcont : ∀ {A B Γ Δ} → Γ ⁏ (Δ , A) , A ⊢ B → Γ ⁏ Δ , A ⊢ B
mcont t = mdet (app ccont (mlam (mlam t)))


-- Exchange.

cexch : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▷ B ▷ C) ▷ B ▷ A ▷ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ Δ} → (Γ , A) , B ⁏ Δ ⊢ C → (Γ , B) , A ⁏ Δ ⊢ C
exch t = det (det (app cexch (lam (lam t))))

mexch : ∀ {A B C Γ Δ} → Γ ⁏ (Δ , A) , B ⊢ C → Γ ⁏ (Δ , B) , A ⊢ C
mexch t = mdet (mdet (app cexch (mlam (mlam t))))


-- Composition.

ccomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ Δ} → Γ , B ⁏ Δ ⊢ C → Γ , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))

mcomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ , B ⊢ □ C → Γ ⁏ Δ , A ⊢ □ B → Γ ⁏ Δ , A ⊢ □ C
mcomp t u = mdet (app (app ccomp (mlam t)) (mlam u))


-- Useful theorems in functional form.

dist : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ▷ B) → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app mv₁ mv₀)))

up : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ □ A
up t = unbox t (box (box mv₀))

down : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ A
down t = unbox t mv₀

distup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▷ B) → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ ⊢ □ B
distup t u = dist t (up u)


-- Useful theorems in combinatory form.

ci : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A ▷ A
ci = lam v₀

ck : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▷ B ▷ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (A ▷ B) ▷ □ A ▷ □ B
cdist = lam (lam (dist v₁ v₀))

cup : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A ▷ □ □ A
cup = lam (up v₀)

cdown : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ □ A ▷ A
cdown = lam (down v₀)

cdistup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ (□ A ▷ B) ▷ □ A ▷ □ B
cdistup = lam (lam (dist v₁ (up v₀)))

cunbox : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ □ A ▷ (□ A ▷ C) ▷ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▷ B ▷ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▷ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▷ B
csnd = lam (snd v₀)


-- Internalisation, or lifting, and additional theorems.

lift : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → □⋆ Γ ⁏ Δ ⊢ □ A
lift {⌀}     t = box t
lift {Γ , B} t = det (app cdist (lift (lam t)))

negup : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ □ □ A ▷ B → Γ ⁏ Δ ⊢ □ A ▷ B
negup t = lam (app (mono⊢ weak⊆ t) (up v₀))

negdown : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▷ B → Γ ⁏ Δ ⊢ □ A ▷ B
negdown t = lam (app (mono⊢ weak⊆ t) (down v₀))

up⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Π → Γ ⁏ Δ ⊢⋆ □⋆ □⋆ Π
up⋆ {⌀}     ∙        = ∙
up⋆ {Π , A} (ts , t) = up⋆ ts , up t

multibox : ∀ {Π A Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Π → □⋆ Π ⁏ ⌀ ⊢ A → Γ ⁏ Δ ⊢ □ A
multibox ts u = multicut (up⋆ ts) (mmono⊢ bot⊆ (lift u))


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ {Δ} → Γ , A ⁏ Δ ⊢ B → Γ′ ⁏ Δ ⊢ A → Γ ⧺ Γ′ ⁏ Δ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)

mconcat : ∀ {A B Γ Δ} Δ′ → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ′ ⊢ □ A → Γ ⁏ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺ₗ Δ′) (mlam t)) (mmono⊢ weak⊆⧺ᵣ u)


-- Substitution.

[_≔_]_ : ∀ {A B Γ Δ} → (i : A ∈ Γ) → Γ - i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ - i ⁏ Δ ⊢ B
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

[_≔_]⋆_ : ∀ {Π A Γ Δ} → (i : A ∈ Γ) → Γ - i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Π → Γ - i ⁏ Δ ⊢⋆ Π
[_≔_]⋆_ {⌀}     i s ∙        = ∙
[_≔_]⋆_ {Π , B} i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t


-- Modal substitution.

m[_≔_]_ : ∀ {A B Γ Δ} → (i : A ∈ Δ) → ⌀ ⁏ Δ - i ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ - i ⊢ B
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

m[_≔_]⋆_ : ∀ {Π A Γ Δ} → (i : A ∈ Δ) → ⌀ ⁏ Δ - i ⊢ A → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ - i ⊢⋆ Π
m[_≔_]⋆_ {⌀}     i s ∙        = ∙
m[_≔_]⋆_ {Π , B} i s (ts , t) = m[ i ≔ s ]⋆ ts , m[ i ≔ s ] t


-- TODO: Conversion.

infix 0 _⇒_
data _⇒_ {Γ Δ : Cx Ty} : ∀ {A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A → Set where
  refl⇒      : ∀ {A} {t : Γ ⁏ Δ ⊢ A}
                → t ⇒ t
  trans⇒     : ∀ {A} {t t′ t″ : Γ ⁏ Δ ⊢ A}
                → t ⇒ t′ → t′ ⇒ t″ → t ⇒ t″
  sym⇒       : ∀ {A} {t t′ : Γ ⁏ Δ ⊢ A}
                → t ⇒ t′ → t′ ⇒ t
  cong⇒lam   : ∀ {A B} {t t′ : Γ , A ⁏ Δ ⊢ B}
                → t ⇒ t′ → lam t ⇒ lam t′
  cong⇒app   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ▷ B} {u u′ : Γ ⁏ Δ ⊢ A}
                → t ⇒ t′ → u ⇒ u′ → app t u ⇒ app t′ u′
  cong⇒pair  : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A} {u u′ : Γ ⁏ Δ ⊢ B}
                → t ⇒ t′ → u ⇒ u′ → pair t u ⇒ pair t′ u′
  cong⇒fst   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⇒ t′ → fst t ⇒ fst t′
  cong⇒snd   : ∀ {A B} {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⇒ t′ → snd t ⇒ snd t′
  -- NOTE: Rejected by Pfenning and Davies.
  -- cong⇒box   : ∀ {A} {t t′ : ⌀ ⁏ Δ ⊢ A}
  --               → t ⇒ t′ → box {Γ} t ⇒ box {Γ} t′
  cong⇒unbox : ∀ {A C} {t t′ : Γ ⁏ Δ ⊢ □ A} {u u′ : Γ ⁏ Δ , A ⊢ C}
                → t ⇒ t′ → u ⇒ u′ → unbox t u ⇒ unbox t′ u′
  conv⇒lam   : ∀ {A B} {t : Γ ⁏ Δ ⊢ A ▷ B}
                → t ⇒ lam (app (mono⊢ weak⊆ t) v₀)
  conv⇒app   : ∀ {A B} {t : Γ , A ⁏ Δ ⊢ B} {u : Γ ⁏ Δ ⊢ A}
                → app (lam t) u ⇒ [ top ≔ u ] t
  conv⇒pair  : ∀ {A B} {t : Γ ⁏ Δ ⊢ A ∧ B}
                → t ⇒ pair (fst t) (snd t)
  conv⇒fst   : ∀ {A B} {t : Γ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ ⊢ B}
                → fst (pair t u) ⇒ t
  conv⇒snd   : ∀ {A B} {t : Γ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ ⊢ B}
                → snd (pair t u) ⇒ u
  conv⇒box   : ∀ {A} {t : Γ ⁏ Δ ⊢ □ A}
                → t ⇒ unbox t (box mv₀)
  conv⇒unbox : ∀ {A C} {t : ⌀ ⁏ Δ ⊢ A} {u : Γ ⁏ Δ , A ⊢ C}
                → unbox (box t) u ⇒ m[ top ≔ t ] u
