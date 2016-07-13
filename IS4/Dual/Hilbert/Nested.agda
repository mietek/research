module IS4.Dual.Hilbert.Nested where

open import IS4.Core public


-- Proofs of IS4, as Hilbert-style combinator trees.

infix 3 _⨾_⊢_
data _⨾_⊢_ (Γ Δ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⨾ Δ ⊢ A
  app   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⊃ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
  ci    : ∀ {A}     → Γ ⨾ Δ ⊢ A ⊃ A
  ck    : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⊃ B ⊃ A
  cs    : ∀ {A B C} → Γ ⨾ Δ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  mvar  : ∀ {A}     → A ∈ Δ → Γ ⨾ Δ ⊢ A
  box   : ∀ {A}     → ⌀ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
  cdist : ∀ {A B}   → Γ ⨾ Δ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B
  cup   : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⊃ □ □ A
  cdown : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⊃ A
  unit  : Γ ⨾ Δ ⊢ ι
  cpair : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⊃ B ⊃ A ∧ B
  cfst  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⊃ A
  csnd  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⊃ B


-- Monotonicity of syntactic consequence with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
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
mono⊢ η unit      = unit
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd


-- Monotonicity with respect to inclusion of modal context.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
mmono⊢ η (var i)   = var i
mmono⊢ η (app t u) = app (mmono⊢ η t) (mmono⊢ η u)
mmono⊢ η ci        = ci
mmono⊢ η ck        = ck
mmono⊢ η cs        = cs
mmono⊢ η (mvar i)  = mvar (mono∈ η i)
mmono⊢ η (box t)   = box (mmono⊢ η t)
mmono⊢ η cdist     = cdist
mmono⊢ η cup       = cup
mmono⊢ η cdown     = cdown
mmono⊢ η unit      = unit
mmono⊢ η cpair     = cpair
mmono⊢ η cfst      = cfst
mmono⊢ η csnd      = csnd


-- Shorthand for variables.

mv₀ : ∀ {A Γ Δ} → Γ ⨾ Δ , A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {A B Γ Δ} → Γ ⨾ Δ , A , B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {A B C Γ Δ} → Γ ⨾ Δ , A , B , C ⊢ A
mv₂ = mvar i₂

v₀ : ∀ {A Γ Δ} → Γ , A ⨾ Δ ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → Γ , A , B ⨾ Δ ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → Γ , A , B , C ⨾ Δ ⊢ A
v₂ = var i₂


-- Deduction theorem.

lam : ∀ {A B Γ Δ} → Γ , A ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ⊃ B
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
lam unit          = app ck unit
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd


-- Combined axioms of distribution and transitivity.

cdistup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⊃ B) ⊃ □ A ⊃ □ B
cdistup = app (app cs (app (app cs (app ck cs))
                           (app (app cs (app (app cs (app ck cs))
                                             (lam (lam cdist))))
                                (app (app cs (app ck ck)) ci))))
              (app (app cs (app (app cs (app ck cs))
                                (lam (lam cup))))
                   (app ck ci))


-- Modal deduction theorem.

mlam : ∀ {A B Γ Δ} → Γ ⨾ Δ , A ⊢ B → Γ ⨾ Δ ⊢ □ A ⊃ B
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
mlam unit           = app ck unit
mlam cpair          = app ck cpair
mlam cfst           = app ck cfst
mlam csnd           = app ck csnd


-- Detachment theorems.

det : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⊃ B → Γ , A ⨾ Δ ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

mdet : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ A ⊃ B → Γ ⨾ Δ , A ⊢ B
mdet t = app (mmono⊢ weak⊆ t) (box mv₀)


-- Contraction.

ccont : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ (A ⊃ A ⊃ B) ⊃ A ⊃ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ Δ} → Γ , A , A ⨾ Δ ⊢ B → Γ , A ⨾ Δ ⊢ B
cont t = det (app ccont (lam (lam t)))

mcont : ∀ {A B Γ Δ} → Γ ⨾ Δ , A , A ⊢ B → Γ ⨾ Δ , A ⊢ B
mcont t = mdet (app ccont (mlam (mlam t)))


-- Exchange.

cexch : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ (A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ Δ} → Γ , A , B ⨾ Δ ⊢ C → Γ , B , A ⨾ Δ ⊢ C
exch t = det (det (app cexch (lam (lam t))))

mexch : ∀ {A B C Γ Δ} → Γ ⨾ Δ , A , B ⊢ C → Γ ⨾ Δ , B , A ⊢ C
mexch t = mdet (mdet (app cexch (mlam (mlam t))))


-- Composition.

ccomp : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ (B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ Δ} → Γ , B ⨾ Δ ⊢ C → Γ , A ⨾ Δ ⊢ B → Γ , A ⨾ Δ ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))

mcomp : ∀ {A B C Γ Δ} → Γ ⨾ Δ , B ⊢ □ C → Γ ⨾ Δ , A ⊢ □ B → Γ ⨾ Δ , A ⊢ □ C
mcomp t u = mdet (app (app ccomp (mlam t)) (mlam u))


-- Useful theorems in functional form.

dist : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (A ⊃ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
dist t u = app (app cdist t) u

up : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ □ A
up t = app cup t

down : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ A
down t = app cdown t

distup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⊃ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
distup t u = dist t (up u)

unbox : ∀ {A C Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ , A ⊢ C → Γ ⨾ Δ ⊢ C
unbox t u = app (mlam u) t

pair : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ B
snd t = app csnd t


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ {Δ} → Γ , A ⨾ Δ ⊢ B → Γ′ ⨾ Δ ⊢ A → Γ ⧺ Γ′ ⨾ Δ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)

mconcat : ∀ {A B Γ Δ} Δ′ → Γ ⨾ Δ , A ⊢ B → Γ ⨾ Δ′ ⊢ □ A → Γ ⨾ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺ₗ Δ′) (mlam t)) (mmono⊢ weak⊆⧺ᵣ u)
