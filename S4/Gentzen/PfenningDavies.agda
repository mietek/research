module S4.Gentzen.PfenningDavies where

open import S4.Core public


-- Proofs of S4, as Gentzen-style natural deduction trees, following Pfenning and Davies.

infix 0 _⨾_⊢_
data _⨾_⊢_ (Γ Δ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⨾ Δ ⊢ A
  lam   : ∀ {A B}   → Γ , A ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ⇒ B
  app   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ⇒ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
  mvar  : ∀ {A}     → A ∈ Δ → Γ ⨾ Δ ⊢ A
  box   : ∀ {A}     → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
  unbox : ∀ {A C}   → Γ ⨾ Δ ⊢ □ A → Γ ⨾ Δ , A ⊢ C → Γ ⨾ Δ ⊢ C
  pair  : ∀ {A B}   → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∧ B
  fst   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ A
  snd   : ∀ {A B}   → Γ ⨾ Δ ⊢ A ∧ B → Γ ⨾ Δ ⊢ B
  inl   : ∀ {A B}   → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A ∨ B
  inr   : ∀ {A B}   → Γ ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ∨ B
  case  : ∀ {A B C} → Γ ⨾ Δ ⊢ A ∨ B → Γ , A ⨾ Δ ⊢ C → Γ , B ⨾ Δ ⊢ C → Γ ⨾ Δ ⊢ C
  boom  : ∀ {C}     → Γ ⨾ Δ ⊢ ⊥ → Γ ⨾ Δ ⊢ C


-- Monotonicity of syntactic consequence.

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (var i)      = var (mono∈ η i)
mono⊢ η (lam t)      = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)    = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (mvar i)     = mvar i
mono⊢ η (box t)      = box t
mono⊢ η (unbox t u)  = unbox (mono⊢ η t) (mono⊢ η u)
mono⊢ η (pair t u)   = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)      = fst (mono⊢ η t)
mono⊢ η (snd t)      = snd (mono⊢ η t)
mono⊢ η (inl t)      = inl (mono⊢ η t)
mono⊢ η (inr t)      = inr (mono⊢ η t)
mono⊢ η (case t u v) = case (mono⊢ η t) (mono⊢ (keep η) u) (mono⊢ (keep η) v)
mono⊢ η (boom t)     = boom (mono⊢ η t)


-- Modal monotonicity.

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
mmono⊢ η (var i)      = var i
mmono⊢ η (lam t)      = lam (mmono⊢ η t)
mmono⊢ η (app t u)    = app (mmono⊢ η t) (mmono⊢ η u)
mmono⊢ η (mvar i)     = mvar (mono∈ η i)
mmono⊢ η (box t)      = box (mmono⊢ η t)
mmono⊢ η (unbox t u)  = unbox (mmono⊢ η t) (mmono⊢ (keep η) u)
mmono⊢ η (pair t u)   = pair (mmono⊢ η t) (mmono⊢ η u)
mmono⊢ η (fst t)      = fst (mmono⊢ η t)
mmono⊢ η (snd t)      = snd (mmono⊢ η t)
mmono⊢ η (inl t)      = inl (mmono⊢ η t)
mmono⊢ η (inr t)      = inr (mmono⊢ η t)
mmono⊢ η (case t u v) = case (mmono⊢ η t) (mmono⊢ η u) (mmono⊢ η v)
mmono⊢ η (boom t)     = boom (mmono⊢ η t)


-- Shorthand for variables.

mv₀ : ∀ {A Γ Δ} → Γ ⨾ Δ , A ⊢ A
mv₀ = mvar top

mv₁ : ∀ {A B Γ Δ} → Γ ⨾ Δ , A , B ⊢ A
mv₁ = mvar (pop top)

mv₂ : ∀ {A B C Γ Δ} → Γ ⨾ Δ , A , B , C ⊢ A
mv₂ = mvar (pop (pop top))

v₀ : ∀ {A Γ Δ} → Γ , A ⨾ Δ ⊢ A
v₀ = var top

v₁ : ∀ {A B Γ Δ} → Γ , A , B ⨾ Δ ⊢ A
v₁ = var (pop top)

v₂ : ∀ {A B C Γ Δ} → Γ , A , B , C ⨾ Δ ⊢ A
v₂ = var (pop (pop top))


-- Deduction theorems.

ded : ∀ {A B Γ Δ} → Γ , A ⨾ Δ ⊢ B → Γ ⨾ Δ ⊢ A ⇒ B
ded t = lam t

mded : ∀ {A B Γ Δ} → Γ ⨾ Δ , A ⊢ B → Γ ⨾ Δ ⊢ □ A ⇒ B
mded t = lam (unbox v₀ (mono⊢ weak⊆ t))


-- Useful theorems in combinatory form.

ci : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ A
ci = lam v₀

ck : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
cdist = lam (lam (unbox v₁ (unbox v₀ (box (app mv₁ mv₀)))))

cup : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A ⇒ □ □ A
cup = lam (unbox v₀ (box (box mv₀)))

cdown : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ □ A ⇒ A
cdown = lam (unbox v₀ mv₀)

cdistup : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ □ (□ A ⇒ B) ⇒ □ A ⇒ □ B
cdistup = lam (lam (app (app cdist v₁) (app cup v₀)))

cpair : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ B ⇒ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B ⇒ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ∧ B ⇒ B
csnd = lam (snd v₀)

cinl : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ A ∨ B
cinl = lam (inl v₀)

cinr : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ B ⇒ A ∨ B
cinr = lam (inr v₀)

ccase : ∀ {A B C Γ Δ} → Γ ⨾ Δ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
ccase = lam (lam (lam (case v₂ (app v₂ v₀) (app v₁ v₀))))

cboom : ∀ {C Γ Δ} → Γ ⨾ Δ ⊢ ⊥ ⇒ C
cboom = lam (boom v₀)
