module S4.Hilbert.Linear where

open import S4.Core public


-- Proofs of S4, as Hilbert-style combinator sequences.

mutual
  infix 1 _⨾_⊢ₛ_
  data _⨾_⊢ₛ_ (Γ Δ : Cx Ty) : Cx Ty → Set where
    nil   : Γ ⨾ Δ ⊢ₛ ⌀
    var   : ∀ {Π A}     → A ∈ Γ → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A
    mp    : ∀ {Π A B}   → A ⊃ B ∈ Π → A ∈ Π → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , B
    ci    : ∀ {Π A}     → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A ⊃ A
    ck    : ∀ {Π A B}   → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A ⊃ B ⊃ A
    cs    : ∀ {Π A B C} → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
    mvar  : ∀ {Π A}     → A ∈ Δ → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A
    nec   : ∀ {Π A}     → ⌀ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , □ A
    cdist : ∀ {Π A B}   → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , □ (A ⊃ B) ⊃ □ A ⊃ □ B
    cup   : ∀ {Π A}     → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , □ A ⊃ □ □ A
    cdown : ∀ {Π A}     → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , □ A ⊃ A
    unit  : ∀ {Π}       → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , ι
    cpair : ∀ {Π A B}   → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A ⊃ B ⊃ A ∧ B
    cfst  : ∀ {Π A B}   → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A ∧ B ⊃ A
    csnd  : ∀ {Π A B}   → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π , A ∧ B ⊃ B

  infix 1 _⨾_⊢_
  _⨾_⊢_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⨾ Δ ⊢ A = Σ (Cx Ty) (λ Π → Γ ⨾ Δ ⊢ₛ Π , A)


-- Monotonicity of syntactic consequence with respect to context inclusion.

mono⊢ₛ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ₛ Π → Γ′ ⨾ Δ ⊢ₛ Π
mono⊢ₛ η nil         = nil
mono⊢ₛ η (var i ts)  = var (mono∈ η i) (mono⊢ₛ η ts)
mono⊢ₛ η (mp i j ts) = mp i j (mono⊢ₛ η ts)
mono⊢ₛ η (ci ts)     = ci (mono⊢ₛ η ts)
mono⊢ₛ η (ck ts)     = ck (mono⊢ₛ η ts)
mono⊢ₛ η (cs ts)     = cs (mono⊢ₛ η ts)
mono⊢ₛ η (mvar i ts) = mvar i (mono⊢ₛ η ts)
mono⊢ₛ η (nec ss ts) = nec ss (mono⊢ₛ η ts)
mono⊢ₛ η (cdist ts)  = cdist (mono⊢ₛ η ts)
mono⊢ₛ η (cup ts)    = cup (mono⊢ₛ η ts)
mono⊢ₛ η (cdown ts)  = cdown (mono⊢ₛ η ts)
mono⊢ₛ η (unit ts)   = unit (mono⊢ₛ η ts)
mono⊢ₛ η (cpair ts)  = cpair (mono⊢ₛ η ts)
mono⊢ₛ η (cfst ts)   = cfst (mono⊢ₛ η ts)
mono⊢ₛ η (csnd ts)   = csnd (mono⊢ₛ η ts)

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢ₛ η ts


-- Monotonicity with respect to inclusion of modal context.

mutual
  mmono⊢ₛ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ′ ⊢ₛ Π
  mmono⊢ₛ η nil         = nil
  mmono⊢ₛ η (var i ts)  = var i (mmono⊢ₛ η ts)
  mmono⊢ₛ η (mp i j ts) = mp i j (mmono⊢ₛ η ts)
  mmono⊢ₛ η (ci ts)     = ci (mmono⊢ₛ η ts)
  mmono⊢ₛ η (ck ts)     = ck (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cs ts)     = cs (mmono⊢ₛ η ts)
  mmono⊢ₛ η (mvar i ts) = mvar (mono∈ η i) (mmono⊢ₛ η ts)
  mmono⊢ₛ η (nec ss ts) = nec (mmono⊢ η ss) (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cdist ts)  = cdist (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cup ts)    = cup (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cdown ts)  = cdown (mmono⊢ₛ η ts)
  mmono⊢ₛ η (unit ts)   = unit (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cpair ts)  = cpair (mmono⊢ₛ η ts)
  mmono⊢ₛ η (cfst ts)   = cfst (mmono⊢ₛ η ts)
  mmono⊢ₛ η (csnd ts)   = csnd (mmono⊢ₛ η ts)

  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
  mmono⊢ η (Π ∙ ts) = Π ∙ mmono⊢ₛ η ts


-- Proof concatenation.

_⧺ₛ_ : ∀ {Γ Δ Π Π′} → Γ ⨾ Δ ⊢ₛ Π → Γ ⨾ Δ ⊢ₛ Π′ → Γ ⨾ Δ ⊢ₛ Π ⧺ Π′
us ⧺ₛ nil       = us
us ⧺ₛ var i ts  = var i (us ⧺ₛ ts)
us ⧺ₛ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧺ₛ ts)
us ⧺ₛ ci ts     = ci (us ⧺ₛ ts)
us ⧺ₛ ck ts     = ck (us ⧺ₛ ts)
us ⧺ₛ cs ts     = cs (us ⧺ₛ ts)
us ⧺ₛ mvar i ts = mvar i (us ⧺ₛ ts)
us ⧺ₛ nec ss ts = nec ss (us ⧺ₛ ts)
us ⧺ₛ cdist ts  = cdist (us ⧺ₛ ts)
us ⧺ₛ cup ts    = cup (us ⧺ₛ ts)
us ⧺ₛ cdown ts  = cdown (us ⧺ₛ ts)
us ⧺ₛ unit ts   = unit (us ⧺ₛ ts)
us ⧺ₛ cpair ts  = cpair (us ⧺ₛ ts)
us ⧺ₛ cfst ts   = cfst (us ⧺ₛ ts)
us ⧺ₛ csnd ts   = csnd (us ⧺ₛ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⊃ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (Π′ , A) ⧺ (Π , A ⊃ B) ∙ mp top (mono∈ (weak⊆⧺ₗ (Π , A ⊃ B)) top) (us ⧺ₛ ts)

box : ∀ {A Γ Δ} → ⌀ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
box ts = ⌀ ∙ nec ts nil
