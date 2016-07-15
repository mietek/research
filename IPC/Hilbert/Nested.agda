module IPC.Hilbert.Nested where

open import IPC.Core public


-- Derivations, as Hilbert-style combinator trees.

infix 3 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  app   : ∀ {A B}   → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
  ci    : ∀ {A}     → Γ ⊢ A ▷ A
  ck    : ∀ {A B}   → Γ ⊢ A ▷ B ▷ A
  cs    : ∀ {A B C} → Γ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
  cpair : ∀ {A B}   → Γ ⊢ A ▷ B ▷ A ∧ B
  cfst  : ∀ {A B}   → Γ ⊢ A ∧ B ▷ A
  csnd  : ∀ {A B}   → Γ ⊢ A ∧ B ▷ B
  tt    : Γ ⊢ ⊤
  cboom : ∀ {C}     → Γ ⊢ ⊥ ▷ C
  cinl  : ∀ {A B}   → Γ ⊢ A ▷ A ∨ B
  cinr  : ∀ {A B}   → Γ ⊢ B ▷ A ∨ B
  ccase : ∀ {A B C} → Γ ⊢ A ∨ B ▷ (A ▷ C) ▷ (B ▷ C) ▷ C


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η tt        = tt
mono⊢ η cboom     = cboom
mono⊢ η cinl      = cinl
mono⊢ η cinr      = cinr
mono⊢ η ccase     = ccase


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → Γ , A , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
v₂ = var i₂


-- Deduction theorem.

lam : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ▷ B
lam (var top)     = ci
lam (var (pop i)) = app ck (var i)
lam (app t u)     = app (app cs (lam t)) (lam u)
lam ci            = app ck ci
lam ck            = app ck ck
lam cs            = app ck cs
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd
lam tt            = app ck tt
lam cboom         = app ck cboom
lam cinl          = app ck cinl
lam cinr          = app ck cinr
lam ccase         = app ck ccase


-- Detachment theorem.

det : ∀ {A B Γ} → Γ ⊢ A ▷ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Contraction.

ccont : ∀ {A B Γ} → Γ ⊢ (A ▷ A ▷ B) ▷ A ▷ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → Γ , A , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ B ▷ A ▷ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → Γ , A , B ⊢ C → Γ , B , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
snd t = app csnd t

boom : ∀ {C Γ} → Γ ⊢ ⊥ → Γ ⊢ C
boom t = app cboom t

inl : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ A ∨ B
inl t = app cinl t

inr : ∀ {A B Γ} → Γ ⊢ B → Γ ⊢ A ∨ B
inr t = app cinr t

case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
case t u v = app (app (app ccase t) (lam u)) (lam v)


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)
