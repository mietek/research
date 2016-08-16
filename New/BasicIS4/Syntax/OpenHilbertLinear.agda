module New.BasicIS4.Syntax.OpenHilbertLinear where

open import New.BasicIS4.Syntax.Common public


-- Derivations, as Hilbert-style lists of combinators, with context.

infix 3 _⊢×_
data _⊢×_ (Γ : Cx Ty) : Cx Ty → Set where
  nil   : Γ ⊢× ⌀
  var   : ∀ {Π A}     → A ∈ Γ → Γ ⊢× Π → Γ ⊢× Π , A
  mp    : ∀ {Π A B}   → A ▻ B ∈ Π → A ∈ Π → Γ ⊢× Π → Γ ⊢× Π , B
  ci    : ∀ {Π A}     → Γ ⊢× Π → Γ ⊢× Π , A ▻ A
  ck    : ∀ {Π A B}   → Γ ⊢× Π → Γ ⊢× Π , A ▻ B ▻ A
  cs    : ∀ {Π A B C} → Γ ⊢× Π → Γ ⊢× Π , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  nec   : ∀ {Π Ξ A}   → ⌀ ⊢× Ξ , A → Γ ⊢× Π → Γ ⊢× Π , □ A
  cdist : ∀ {Π A B}   → Γ ⊢× Π → Γ ⊢× Π , □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {Π A}     → Γ ⊢× Π → Γ ⊢× Π , □ A ▻ □ □ A
  cdown : ∀ {Π A}     → Γ ⊢× Π → Γ ⊢× Π , □ A ▻ A
  cpair : ∀ {Π A B}   → Γ ⊢× Π → Γ ⊢× Π , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Π A B}   → Γ ⊢× Π → Γ ⊢× Π , A ∧ B ▻ A
  csnd  : ∀ {Π A B}   → Γ ⊢× Π → Γ ⊢× Π , A ∧ B ▻ B
  tt    : ∀ {Π}       → Γ ⊢× Π → Γ ⊢× Π , ⊤

infix 3 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = ∃ (λ Π → Γ ⊢× Π , A)


-- Monotonicity with respect to context inclusion.

mono⊢× : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢× Π → Γ′ ⊢× Π
mono⊢× η nil         = nil
mono⊢× η (var i ts)  = var (mono∈ η i) (mono⊢× η ts)
mono⊢× η (mp i j ts) = mp i j (mono⊢× η ts)
mono⊢× η (ci ts)     = ci (mono⊢× η ts)
mono⊢× η (ck ts)     = ck (mono⊢× η ts)
mono⊢× η (cs ts)     = cs (mono⊢× η ts)
mono⊢× η (nec ss ts) = nec ss (mono⊢× η ts)
mono⊢× η (cdist ts)  = cdist (mono⊢× η ts)
mono⊢× η (cup ts)    = cup (mono⊢× η ts)
mono⊢× η (cdown ts)  = cdown (mono⊢× η ts)
mono⊢× η (cpair ts)  = cpair (mono⊢× η ts)
mono⊢× η (cfst ts)   = cfst (mono⊢× η ts)
mono⊢× η (csnd ts)   = csnd (mono⊢× η ts)
mono⊢× η (tt ts)     = tt (mono⊢× η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π , ts) = Π , mono⊢× η ts


-- Derivation concatenation.

_⧻_ : ∀ {Γ Π Π′} → Γ ⊢× Π → Γ ⊢× Π′ → Γ ⊢× Π ⧺ Π′
us ⧻ nil       = us
us ⧻ var i ts  = var i (us ⧻ ts)
us ⧻ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧻ ts)
us ⧻ ci ts     = ci (us ⧻ ts)
us ⧻ ck ts     = ck (us ⧻ ts)
us ⧻ cs ts     = cs (us ⧻ ts)
us ⧻ nec ss ts = nec ss (us ⧻ ts)
us ⧻ cdist ts  = cdist (us ⧻ ts)
us ⧻ cup ts    = cup (us ⧻ ts)
us ⧻ cdown ts  = cdown (us ⧻ ts)
us ⧻ cpair ts  = cpair (us ⧻ ts)
us ⧻ cfst ts   = cfst (us ⧻ ts)
us ⧻ csnd ts   = csnd (us ⧻ ts)
us ⧻ tt ts     = tt (us ⧻ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ▻ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π , ts) (Π′ , us) = Π″ , vs
  where Π″ = (Π′ , A) ⧺ (Π , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Π , A ▻ B)) top) (us ⧻ ts)

box : ∀ {A Γ} → ⌀ ⊢ A → Γ ⊢ □ A
box (Π , ts) = ⌀ , nec ts nil
