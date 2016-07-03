module IPC.Hilbert.Nested where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator trees.

infix 1 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var  : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  app  : ∀ {A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ci   : ∀ {A}     → Γ ⊢ A ⇒ A
  ck   : ∀ {A B}   → Γ ⊢ A ⇒ B ⇒ A
  cs   : ∀ {A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  pair : ∀ {A B}   → Γ ⊢ A ⇒ B ⇒ A ∧ B
  fst  : ∀ {A B}   → Γ ⊢ A ∧ B ⇒ A
  snd  : ∀ {A B}   → Γ ⊢ A ∧ B ⇒ B
  inl  : ∀ {A B}   → Γ ⊢ A ⇒ A ∨ B
  inr  : ∀ {A B}   → Γ ⊢ B ⇒ A ∨ B
  case : ∀ {A B C} → Γ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
  boom : ∀ {C}     → Γ ⊢ ⊥ ⇒ C


-- Monotonicity of syntactic consequence.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η pair      = pair
mono⊢ η fst       = fst
mono⊢ η snd       = snd
mono⊢ η inl       = inl
mono⊢ η inr       = inr
mono⊢ η case      = case
mono⊢ η boom      = boom


-- Deduction theorem.

ded : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
ded (var top)     = ci
ded (var (pop i)) = app ck (var i)
ded (app t u)     = app (app cs (ded t)) (ded u)
ded ci            = app ck ci
ded ck            = app ck ck
ded cs            = app ck cs
ded pair          = app ck pair
ded fst           = app ck fst
ded snd           = app ck snd
ded inl           = app ck inl
ded inr           = app ck inr
ded case          = app ck case
ded boom          = app ck boom


-- Useful theorems in functional form.

fpair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
fpair t u = app (app pair t) u

ffst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
ffst t = app fst t

fsnd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
fsnd t = app snd t

finl : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ A ∨ B
finl t = app inl t

finr : ∀ {A B Γ} → Γ ⊢ B → Γ ⊢ A ∨ B
finr t = app inr t

fcase : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
fcase t u v = app (app (app case t) (ded u)) (ded v)

fboom : ∀ {C Γ} → Γ ⊢ ⊥ → Γ ⊢ C
fboom t = app boom t
