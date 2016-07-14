module BasicIS4.Dual.Hilbert.Sequential where

open import BasicIS4.Core public


-- Proofs of IS4, as Hilbert-style combinator sequences.

mutual
  infix 3 _⨾_⊢⋆_
  data _⨾_⊢⋆_ (Γ Δ : Cx Ty) : Cx Ty → Set where
    nil   : Γ ⨾ Δ ⊢⋆ ⌀
    var   : ∀ {Π A}     → A ∈ Γ → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A
    mp    : ∀ {Π A B}   → A ▷ B ∈ Π → A ∈ Π → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , B
    ci    : ∀ {Π A}     → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A ▷ A
    ck    : ∀ {Π A B}   → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A ▷ B ▷ A
    cs    : ∀ {Π A B C} → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
    mvar  : ∀ {Π A}     → A ∈ Δ → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A
    nec   : ∀ {Π A}     → ⌀ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , □ A
    cdist : ∀ {Π A B}   → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , □ (A ▷ B) ▷ □ A ▷ □ B
    cup   : ∀ {Π A}     → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , □ A ▷ □ □ A
    cdown : ∀ {Π A}     → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , □ A ▷ A
    unit  : ∀ {Π}       → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , ⫪
    cpair : ∀ {Π A B}   → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A ▷ B ▷ A ∧ B
    cfst  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A ∧ B ▷ A
    csnd  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π , A ∧ B ▷ B

  infix 3 _⨾_⊢_
  _⨾_⊢_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⨾ Δ ⊢ A = Σ (Cx Ty) (λ Π → Γ ⨾ Δ ⊢⋆ Π , A)


-- Monotonicity with respect to context inclusion.

mono⊢⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢⋆ Π → Γ′ ⨾ Δ ⊢⋆ Π
mono⊢⋆ η nil         = nil
mono⊢⋆ η (var i ts)  = var (mono∈ η i) (mono⊢⋆ η ts)
mono⊢⋆ η (mp i j ts) = mp i j (mono⊢⋆ η ts)
mono⊢⋆ η (ci ts)     = ci (mono⊢⋆ η ts)
mono⊢⋆ η (ck ts)     = ck (mono⊢⋆ η ts)
mono⊢⋆ η (cs ts)     = cs (mono⊢⋆ η ts)
mono⊢⋆ η (mvar i ts) = mvar i (mono⊢⋆ η ts)
mono⊢⋆ η (nec ss ts) = nec ss (mono⊢⋆ η ts)
mono⊢⋆ η (cdist ts)  = cdist (mono⊢⋆ η ts)
mono⊢⋆ η (cup ts)    = cup (mono⊢⋆ η ts)
mono⊢⋆ η (cdown ts)  = cdown (mono⊢⋆ η ts)
mono⊢⋆ η (unit ts)   = unit (mono⊢⋆ η ts)
mono⊢⋆ η (cpair ts)  = cpair (mono⊢⋆ η ts)
mono⊢⋆ η (cfst ts)   = cfst (mono⊢⋆ η ts)
mono⊢⋆ η (csnd ts)   = csnd (mono⊢⋆ η ts)

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⋆ η ts


-- Monotonicity with respect to modal context inclusion.

mutual
  mmono⊢⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ′ ⊢⋆ Π
  mmono⊢⋆ η nil         = nil
  mmono⊢⋆ η (var i ts)  = var i (mmono⊢⋆ η ts)
  mmono⊢⋆ η (mp i j ts) = mp i j (mmono⊢⋆ η ts)
  mmono⊢⋆ η (ci ts)     = ci (mmono⊢⋆ η ts)
  mmono⊢⋆ η (ck ts)     = ck (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cs ts)     = cs (mmono⊢⋆ η ts)
  mmono⊢⋆ η (mvar i ts) = mvar (mono∈ η i) (mmono⊢⋆ η ts)
  mmono⊢⋆ η (nec ss ts) = nec (mmono⊢ η ss) (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cdist ts)  = cdist (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cup ts)    = cup (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cdown ts)  = cdown (mmono⊢⋆ η ts)
  mmono⊢⋆ η (unit ts)   = unit (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cpair ts)  = cpair (mmono⊢⋆ η ts)
  mmono⊢⋆ η (cfst ts)   = cfst (mmono⊢⋆ η ts)
  mmono⊢⋆ η (csnd ts)   = csnd (mmono⊢⋆ η ts)

  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
  mmono⊢ η (Π ∙ ts) = Π ∙ mmono⊢⋆ η ts


-- Proof concatenation.

_⧻_ : ∀ {Γ Δ Π Π′} → Γ ⨾ Δ ⊢⋆ Π → Γ ⨾ Δ ⊢⋆ Π′ → Γ ⨾ Δ ⊢⋆ Π ⧺ Π′
us ⧻ nil       = us
us ⧻ var i ts  = var i (us ⧻ ts)
us ⧻ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧻ ts)
us ⧻ ci ts     = ci (us ⧻ ts)
us ⧻ ck ts     = ck (us ⧻ ts)
us ⧻ cs ts     = cs (us ⧻ ts)
us ⧻ mvar i ts = mvar i (us ⧻ ts)
us ⧻ nec ss ts = nec ss (us ⧻ ts)
us ⧻ cdist ts  = cdist (us ⧻ ts)
us ⧻ cup ts    = cup (us ⧻ ts)
us ⧻ cdown ts  = cdown (us ⧻ ts)
us ⧻ unit ts   = unit (us ⧻ ts)
us ⧻ cpair ts  = cpair (us ⧻ ts)
us ⧻ cfst ts   = cfst (us ⧻ ts)
us ⧻ csnd ts   = csnd (us ⧻ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ▷ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (Π′ , A) ⧺ (Π , A ▷ B) ∙ mp top (mono∈ (weak⊆⧺ₗ (Π , A ▷ B)) top) (us ⧻ ts)

box : ∀ {A Γ Δ} → ⌀ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
box ts = ⌀ ∙ nec ts nil
