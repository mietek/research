module S4.Hilbert.Nested where

open import S4.Core public


-- Proofs of S4, as Hilbert-style combinator trees.

infix 1 _⨾_⊢_
data _⨾_⊢_ (Γ Δ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⨾ Δ ⊢ A
  app   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
  ci    : ∀ {A}     → Γ ⨾ Δ ⊢ A ⇒ A
  ck    : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A
  cs    : ∀ {A B C} → Γ ⨾ Δ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  mvar  : ∀ {A}     → A ∈ Δ → Γ ⨾ Δ ⊢ A
  box   : ∀ {A}     → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
  cdist : ∀ {A B}   → Γ ⨾ Δ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
  cup   : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⇒ □ □ A
  cdown : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⇒ A
  cpair : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A ∧ B
  cfst  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⇒ A
  csnd  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⇒ B
  cinl  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ A ∨ B
  cinr  : ∀ {A B}   → Γ ⨾ Δ ⊢ B ⇒ A ∨ B
  ccase : ∀ {A B C} → Γ ⨾ Δ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
  cboom : ∀ {C}     → Γ ⨾ Δ ⊢ ⊥ ⇒ C


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app i j) = app (mono⊢ η i) (mono⊢ η j)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η (mvar i)  = mvar i
mono⊢ η (box i)   = box i
mono⊢ η cdist     = cdist
mono⊢ η cup       = cup
mono⊢ η cdown     = cdown
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η cinl      = cinl
mono⊢ η cinr      = cinr
mono⊢ η ccase     = ccase
mono⊢ η cboom     = cboom


-- Monotonicity of syntactic consequence with respect to modal context extension.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
mmono⊢ η (var i)   = var i
mmono⊢ η (app i j) = app (mmono⊢ η i) (mmono⊢ η j)
mmono⊢ η ci        = ci
mmono⊢ η ck        = ck
mmono⊢ η cs        = cs
mmono⊢ η (mvar i)  = mvar (mono∈ η i)
mmono⊢ η (box i)   = box (mmono⊢ η i)
mmono⊢ η cdist     = cdist
mmono⊢ η cup       = cup
mmono⊢ η cdown     = cdown
mmono⊢ η cpair     = cpair
mmono⊢ η cfst      = cfst
mmono⊢ η csnd      = csnd
mmono⊢ η cinl      = cinl
mmono⊢ η cinr      = cinr
mmono⊢ η ccase     = ccase
mmono⊢ η cboom     = cboom


-- Deduction theorem.

lam : ∀ {A B Γ Δ} → Γ , A ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ⇒ B
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
lam cinl          = app ck cinl
lam cinr          = app ck cinr
lam ccase         = app ck ccase
lam cboom         = app ck cboom


-- Combined axioms of distribution and transitivity.

cdistup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⇒ B) ⇒ □ A ⇒ □ B
cdistup = app (app cs (app (app cs (app ck cs))
                           (app (app cs (app (app cs (app ck cs))
                                             (lam (lam cdist))))
                                (app (app cs (app ck ck)) ci))))
              (app (app cs (app (app cs (app ck cs))
                                (lam (lam cup))))
                   (app ck ci))


-- Modal deduction theorem.

mlam : ∀ {A B Γ Δ} → Γ ⨾ Δ , A ⊢ B → Γ ⨾ Δ ⊢ □ A ⇒ B
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
mlam cinl           = app ck cinl
mlam cinr           = app ck cinr
mlam ccase          = app ck ccase
mlam cboom          = app ck cboom


-- Useful theorems in functional form.

dist : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (A ⇒ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
dist t u = app (app cdist t) u

up : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ □ A
up t = app cup t

down : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ A
down t = app cdown t

distup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⇒ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
distup t u = dist t (up u)

unbox : ∀ {A C Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ , A ⊢ C → Γ ⨾ Δ ⊢ C
unbox t u = app (mlam u) t

pair : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ B
snd t = app csnd t

inl : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A ∨ B
inl t = app cinl t

inr : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∨ B
inr t = app cinr t

case : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ A ∨ B → Γ , A ⨾ Δ ⊢ C → Γ , B ⨾ Δ ⊢ C → Γ ⨾ Δ ⊢ C
case t u v = app (app (app ccase t) (lam u)) (lam v)

boom : ∀ {C Γ Δ} → Γ ⨾ Δ ⊢ ⊥ → Γ ⨾ Δ ⊢ C
boom t = app cboom t
