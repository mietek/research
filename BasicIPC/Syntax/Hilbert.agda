-- Hilbert-style axiomatic formalisation of syntax.

module BasicIPC.Syntax.Hilbert where

open import BasicIPC.Syntax.Common public


-- Derivations.

infix 3 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var   : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  app   : ∀ {A B}   → Γ ⊢ A ▻ B → Γ ⊢ A → Γ ⊢ B
  ci    : ∀ {A}     → Γ ⊢ A ▻ A
  ck    : ∀ {A B}   → Γ ⊢ A ▻ B ▻ A
  cs    : ∀ {A B C} → Γ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  cpair : ∀ {A B}   → Γ ⊢ A ▻ B ▻ A ∧ B
  cfst  : ∀ {A B}   → Γ ⊢ A ∧ B ▻ A
  csnd  : ∀ {A B}   → Γ ⊢ A ∧ B ▻ B
  tt    : Γ ⊢ ⊤

infix 3 _⊢⋆_
_⊢⋆_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ ⌀     = 𝟙
Γ ⊢⋆ Π , A = Γ ⊢⋆ Π × Γ ⊢ A


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

mono⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Π → Γ′ ⊢⋆ Π
mono⊢⋆ {⌀}     η ∙        = ∙
mono⊢⋆ {Π , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → (Γ , A) , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → ((Γ , A) , B) , C ⊢ A
v₂ = var i₂


-- Deduction theorem.

lam : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ▻ B
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

lam⋆ : ∀ {Π Γ A} → Γ ⧺ Π ⊢ A → Γ ⊢ Π ▻⋯▻ A
lam⋆ {⌀}     = id
lam⋆ {Π , B} = lam⋆ {Π} ∘ lam

lam⋆₀ : ∀ {Γ A} → Γ ⊢ A → ⌀ ⊢ Γ ▻⋯▻ A
lam⋆₀ {⌀}     = id
lam⋆₀ {Γ , B} = lam⋆₀ ∘ lam


-- Detachment theorem.

det : ∀ {A B Γ} → Γ ⊢ A ▻ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

det⋆ : ∀ {Π Γ A} → Γ ⊢ Π ▻⋯▻ A → Γ ⧺ Π ⊢ A
det⋆ {⌀}     = id
det⋆ {Π , B} = det ∘ det⋆ {Π}

det⋆₀ : ∀ {Γ A} → ⌀ ⊢ Γ ▻⋯▻ A → Γ ⊢ A
det⋆₀ {⌀}     = id
det⋆₀ {Γ , B} = det ∘ det⋆₀


-- Cut and multicut.

cut : ∀ {A B Γ} → Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
cut t u = app (lam u) t

multicut : ∀ {Π A Γ} → Γ ⊢⋆ Π → Π ⊢ A → Γ ⊢ A
multicut {⌀}     ∙        u = mono⊢ bot⊆ u
multicut {Π , B} (ts , t) u = app (multicut ts (lam u)) t


-- Reflexivity and transitivity.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {⌀}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

trans⊢⋆ : ∀ {Γ″ Γ′ Γ} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Γ″ → Γ ⊢⋆ Γ″
trans⊢⋆ {⌀}      ts ∙        = ∙
trans⊢⋆ {Γ″ , A} ts (us , u) = trans⊢⋆ ts us , multicut ts u


-- Contraction.

ccont : ∀ {A B Γ} → Γ ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → (Γ , A) , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → (Γ , A) , B ⊢ C → (Γ , B) , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
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


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)


-- Conversion.

data _⇒_ {Γ : Cx Ty} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl⇒     : ∀ {A} {t : Γ ⊢ A}
               → t ⇒ t
  trans⇒    : ∀ {A} {t t′ t″ : Γ ⊢ A}
               → t ⇒ t′ → t′ ⇒ t″ → t ⇒ t″
  sym⇒      : ∀ {A} {t t′ : Γ ⊢ A}
               → t ⇒ t′ → t′ ⇒ t
  congapp⇒  : ∀ {A B} {t t′ : Γ ⊢ A ▻ B} {u u′ : Γ ⊢ A}
               → t ⇒ t′ → u ⇒ u′
               → app t u ⇒ app t′ u′
  congi⇒    : ∀ {A} {t t′ : Γ ⊢ A}
               → t ⇒ t′
               → app ci t ⇒ app ci t′
  congk⇒    : ∀ {A B} {t t′ : Γ ⊢ A} {u u′ : Γ ⊢ B}
               → t ⇒ t′ → u ⇒ u′
               → app (app ck t) u ⇒ app (app ck t′) u′
  congs⇒    : ∀ {A B C} {t t′ : Γ ⊢ A ▻ B ▻ C} {u u′ : Γ ⊢ A ▻ B} {v v′ : Γ ⊢ A}
               → t ⇒ t′ → u ⇒ u′ → v ⇒ v′
               → app (app (app cs t) u) v ⇒ app (app (app cs t′) u′) v′
  congpair⇒ : ∀ {A B} {t t′ : Γ ⊢ A} {u u′ : Γ ⊢ B}
               → t ⇒ t′ → u ⇒ u′
               → app (app cpair t) u ⇒ app (app cpair t′) u′
  congfst⇒  : ∀ {A B} {t t′ : Γ ⊢ A ∧ B}
               → t ⇒ t′
               → app cfst t ⇒ app cfst t′
  congsnd⇒  : ∀ {A B} {t t′ : Γ ⊢ A ∧ B}
               → t ⇒ t′
               → app csnd t ⇒ app csnd t′
  -- TODO: Verify this.
  beta▻ₖ⇒   : ∀ {A B} {t : Γ ⊢ A} {u : Γ ⊢ B}
               → app (app ck t) u ⇒ t
  -- TODO: Verify this.
  beta▻ₛ⇒   : ∀ {A B C} {t : Γ ⊢ A ▻ B ▻ C} {u : Γ ⊢ A ▻ B} {v : Γ ⊢ A}
               → app (app (app cs t) u) v ⇒ app (app t v) (app u v)
  -- TODO: What about eta for ▻?
  beta∧₁⇒   : ∀ {A B} {t : Γ ⊢ A} {u : Γ ⊢ B}
               → app cfst (app (app cpair t) u) ⇒ t
  beta∧₂⇒   : ∀ {A B} {t : Γ ⊢ A} {u : Γ ⊢ B}
               → app csnd (app (app cpair t) u) ⇒ u
  eta∧⇒     : ∀ {A B} {t : Γ ⊢ A ∧ B}
               → t ⇒ app (app cpair (app cfst t)) (app csnd t)
  eta⊤⇒    : ∀ {t : Γ ⊢ ⊤}
               → t ⇒ tt
