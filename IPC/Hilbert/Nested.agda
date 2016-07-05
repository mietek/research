module IPC.Hilbert.Nested where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator trees.

infix 1 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  app   : ∀ {A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ci    : ∀ {A}     → Γ ⊢ A ⇒ A
  ck    : ∀ {A B}   → Γ ⊢ A ⇒ B ⇒ A
  cs    : ∀ {A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  cpair : ∀ {A B}   → Γ ⊢ A ⇒ B ⇒ A ∧ B
  cfst  : ∀ {A B}   → Γ ⊢ A ∧ B ⇒ A
  csnd  : ∀ {A B}   → Γ ⊢ A ∧ B ⇒ B
  cinl  : ∀ {A B}   → Γ ⊢ A ⇒ A ∨ B
  cinr  : ∀ {A B}   → Γ ⊢ B ⇒ A ∨ B
  ccase : ∀ {A B C} → Γ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
  cboom : ∀ {C}     → Γ ⊢ ⊥ ⇒ C


-- Monotonicity of syntactic consequence with respect to intuitionistic context extensions.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η cinl      = cinl
mono⊢ η cinr      = cinr
mono⊢ η ccase     = ccase
mono⊢ η cboom     = cboom


-- Deduction theorem.

lam : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
lam (var top)     = ci
lam (var (pop i)) = app ck (var i)
lam (app t u)     = app (app cs (lam t)) (lam u)
lam ci            = app ck ci
lam ck            = app ck ck
lam cs            = app ck cs
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd
lam cinl          = app ck cinl
lam cinr          = app ck cinr
lam ccase         = app ck ccase
lam cboom         = app ck cboom


-- Useful theorems in functional form.

pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
snd t = app csnd t

inl : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ A ∨ B
inl t = app cinl t

inr : ∀ {A B Γ} → Γ ⊢ B → Γ ⊢ A ∨ B
inr t = app cinr t

case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
case t u v = app (app (app ccase t) (lam u)) (lam v)

boom : ∀ {C Γ} → Γ ⊢ ⊥ → Γ ⊢ C
boom t = app cboom t
