module S4.Hilbert.Nested where

open import S4.Core public


-- Proofs of S4, as Hilbert-style combinator trees.

infix 1 _⨾_⊢_
data _⨾_⊢_ (Γ Δ : Cx Ty) : Ty → Set where
  var  : ∀ {A}     → A ∈ Γ → Γ ⨾ Δ ⊢ A
  app  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
  ci   : ∀ {A}     → Γ ⨾ Δ ⊢ A ⇒ A
  ck   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A
  cs   : ∀ {A B C} → Γ ⨾ Δ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  mvar : ∀ {A}     → A ∈ Δ → Γ ⨾ Δ ⊢ A
  nec  : ∀ {A}     → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
  dist : ∀ {A B}   → Γ ⨾ Δ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
  up   : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⇒ □ □ A
  down : ∀ {A}     → Γ ⨾ Δ ⊢ □ A ⇒ A
  pair : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A ∧ B
  fst  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⇒ A
  snd  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B ⇒ B
  inl  : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ A ∨ B
  inr  : ∀ {A B}   → Γ ⨾ Δ ⊢ B ⇒ A ∨ B
  case : ∀ {A B C} → Γ ⨾ Δ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
  boom : ∀ {C}     → Γ ⨾ Δ ⊢ ⊥ ⇒ C


-- Monotonicity of syntactic consequence with respect to truth context extension.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app i j) = app (mono⊢ η i) (mono⊢ η j)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η (mvar i)  = mvar i
mono⊢ η (nec i)   = nec i
mono⊢ η dist      = dist
mono⊢ η up        = up
mono⊢ η down      = down
mono⊢ η pair      = pair
mono⊢ η fst       = fst
mono⊢ η snd       = snd
mono⊢ η inl       = inl
mono⊢ η inr       = inr
mono⊢ η case      = case
mono⊢ η boom      = boom


-- Monotonicity of syntactic consequence with respect to validity context extension.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
mmono⊢ η (var i)   = var i
mmono⊢ η (app i j) = app (mmono⊢ η i) (mmono⊢ η j)
mmono⊢ η ci        = ci
mmono⊢ η ck        = ck
mmono⊢ η cs        = cs
mmono⊢ η (mvar i)  = mvar (mono∈ η i)
mmono⊢ η (nec i)   = nec (mmono⊢ η i)
mmono⊢ η dist      = dist
mmono⊢ η up        = up
mmono⊢ η down      = down
mmono⊢ η pair      = pair
mmono⊢ η fst       = fst
mmono⊢ η snd       = snd
mmono⊢ η inl       = inl
mmono⊢ η inr       = inr
mmono⊢ η case      = case
mmono⊢ η boom      = boom


-- Deduction theorem.

ded : ∀ {A B Γ Δ} → Γ , A ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ⇒ B
ded (var top)     = ci
ded (var (pop i)) = app ck (var i)
ded (app t u)     = app (app cs (ded t)) (ded u)
ded ci            = app ck ci
ded ck            = app ck ck
ded cs            = app ck cs
ded (mvar i)      = app ck (mvar i)
ded (nec t)       = app ck (nec t)
ded dist          = app ck dist
ded up            = app ck up
ded down          = app ck down
ded pair          = app ck pair
ded fst           = app ck fst
ded snd           = app ck snd
ded inl           = app ck inl
ded inr           = app ck inr
ded case          = app ck case
ded boom          = app ck boom


-- Combined axioms of distribution and transitivity.

distup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⇒ B) ⇒ □ A ⇒ □ B
distup = app (app cs (app (app cs (app ck cs))
                          (app (app cs (app (app cs (app ck cs))
                                            (ded (ded dist))))
                               (app (app cs (app ck ck)) ci))))
             (app (app cs (app (app cs (app ck cs))
                               (ded (ded up))))
                  (app ck ci))


-- Modal deduction theorem.

mded : ∀ {A B Γ Δ} → Γ ⨾ Δ , A ⊢ B → Γ ⨾ Δ ⊢ □ A ⇒ B
mded (var i)        = app ck (var i)
mded (app t u)      = app (app cs (mded t)) (mded u)
mded ci             = app ck ci
mded ck             = app ck ck
mded cs             = app ck cs
mded (mvar top)     = down
mded (mvar (pop i)) = app ck (mvar i)
mded (nec t)        = app distup (nec (mded t))
mded dist           = app ck dist
mded up             = app ck up
mded down           = app ck down
mded pair           = app ck pair
mded fst            = app ck fst
mded snd            = app ck snd
mded inl            = app ck inl
mded inr            = app ck inr
mded case           = app ck case
mded boom           = app ck boom


-- Useful theorems in functional form.

funbox : ∀ {A C Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ , A ⊢ C → Γ ⨾ Δ ⊢ C
funbox t u = app (mded u) t

fdist : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (A ⇒ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
fdist t u = app (app dist t) u

fup : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ □ A
fup t = app up t

fdown : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ A
fdown t = app down t

fdistup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⇒ B) → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ ⊢ □ B
fdistup t u = app (app distup t) u

fpair : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∧ B
fpair t u = app (app pair t) u

ffst : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ A
ffst t = app fst t

fsnd : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ B
fsnd t = app snd t

finl : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A ∨ B
finl t = app inl t

finr : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∨ B
finr t = app inr t

fcase : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ A ∨ B → Γ , A ⨾ Δ ⊢ C → Γ , B ⨾ Δ ⊢ C → Γ ⨾ Δ ⊢ C
fcase t u v = app (app (app case t) (ded u)) (ded v)

fboom : ∀ {C Γ Δ} → Γ ⨾ Δ ⊢ ⊥ → Γ ⨾ Δ ⊢ C
fboom t = app boom t
