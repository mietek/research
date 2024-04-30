-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Hilbert-style formalisation of syntax with context pairs.
-- Sequences of terms.

module A201607.BasicIS4.Syntax.DyadicHilbertSequential where

open import A201607.BasicIS4.Syntax.Common public


-- Derivations.

infix 3 _⊦⊢_
data _⊦⊢_ : Cx² Ty Ty → Cx Ty → Set where
  nil   : ∀ {Γ Δ}         → Γ ⁏ Δ ⊦⊢ ∅
  var   : ∀ {Ξ A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A
  mp    : ∀ {Ξ A B Γ Δ}   → A ▻ B ∈ Ξ → A ∈ Ξ → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , B
  ci    : ∀ {Ξ A Γ Δ}     → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A ▻ A
  ck    : ∀ {Ξ A B Γ Δ}   → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C Γ Δ} → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  mvar  : ∀ {Ξ A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A
  nec   : ∀ {Ξ Ξ′ A Γ Δ}  → ∅ ⁏ Δ ⊦⊢ Ξ′ , A → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , □ A
  cdist : ∀ {Ξ A B Γ Δ}   → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {Ξ A Γ Δ}     → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , □ A ▻ □ □ A
  cdown : ∀ {Ξ A Γ Δ}     → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , □ A ▻ A
  cpair : ∀ {Ξ A B Γ Δ}   → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B Γ Δ}   → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B Γ Δ}   → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A ∧ B ▻ B
  unit  : ∀ {Ξ Γ Δ}       → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , ⊤

infix 3 _⊢_
_⊢_ : Cx² Ty Ty → Ty → Set
Γ ⁏ Δ ⊢ A = ∃ (λ Ξ → Γ ⁏ Δ ⊦⊢ Ξ , A)


-- Monotonicity with respect to context inclusion.

mono⊦⊢ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊦⊢ Ξ → Γ′ ⁏ Δ ⊦⊢ Ξ
mono⊦⊢ η nil         = nil
mono⊦⊢ η (var i ts)  = var (mono∈ η i) (mono⊦⊢ η ts)
mono⊦⊢ η (mp i j ts) = mp i j (mono⊦⊢ η ts)
mono⊦⊢ η (ci ts)     = ci (mono⊦⊢ η ts)
mono⊦⊢ η (ck ts)     = ck (mono⊦⊢ η ts)
mono⊦⊢ η (cs ts)     = cs (mono⊦⊢ η ts)
mono⊦⊢ η (mvar i ts) = mvar i (mono⊦⊢ η ts)
mono⊦⊢ η (nec ss ts) = nec ss (mono⊦⊢ η ts)
mono⊦⊢ η (cdist ts)  = cdist (mono⊦⊢ η ts)
mono⊦⊢ η (cup ts)    = cup (mono⊦⊢ η ts)
mono⊦⊢ η (cdown ts)  = cdown (mono⊦⊢ η ts)
mono⊦⊢ η (cpair ts)  = cpair (mono⊦⊢ η ts)
mono⊦⊢ η (cfst ts)   = cfst (mono⊦⊢ η ts)
mono⊦⊢ η (csnd ts)   = csnd (mono⊦⊢ η ts)
mono⊦⊢ η (unit ts)   = unit (mono⊦⊢ η ts)

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ ⊢ A
mono⊢ η (Ξ , ts) = Ξ , mono⊦⊢ η ts


-- Monotonicity with respect to modal context inclusion.

mmono⊦⊢ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ′ ⊦⊢ Ξ
mmono⊦⊢ θ nil         = nil
mmono⊦⊢ θ (var i ts)  = var i (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (mp i j ts) = mp i j (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (ci ts)     = ci (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (ck ts)     = ck (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cs ts)     = cs (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (mvar i ts) = mvar (mono∈ θ i) (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (nec ss ts) = nec (mmono⊦⊢ θ ss) (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cdist ts)  = cdist (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cup ts)    = cup (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cdown ts)  = cdown (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cpair ts)  = cpair (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (cfst ts)   = cfst (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (csnd ts)   = csnd (mmono⊦⊢ θ ts)
mmono⊦⊢ θ (unit ts)   = unit (mmono⊦⊢ θ ts)

mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
mmono⊢ θ (Ξ , ts) = Ξ , mmono⊦⊢ θ ts


-- Concatenation of derivations.

_⧺⊦_ : ∀ {Γ Δ Ξ Ξ′} → Γ ⁏ Δ ⊦⊢ Ξ → Γ ⁏ Δ ⊦⊢ Ξ′ → Γ ⁏ Δ ⊦⊢ Ξ ⧺ Ξ′
us ⧺⊦ nil       = us
us ⧺⊦ var i ts  = var i (us ⧺⊦ ts)
us ⧺⊦ mp i j ts = mp (mono∈ weak⊆⧺₂ i) (mono∈ weak⊆⧺₂ j) (us ⧺⊦ ts)
us ⧺⊦ ci ts     = ci (us ⧺⊦ ts)
us ⧺⊦ ck ts     = ck (us ⧺⊦ ts)
us ⧺⊦ cs ts     = cs (us ⧺⊦ ts)
us ⧺⊦ mvar i ts = mvar i (us ⧺⊦ ts)
us ⧺⊦ nec ss ts = nec ss (us ⧺⊦ ts)
us ⧺⊦ cdist ts  = cdist (us ⧺⊦ ts)
us ⧺⊦ cup ts    = cup (us ⧺⊦ ts)
us ⧺⊦ cdown ts  = cdown (us ⧺⊦ ts)
us ⧺⊦ cpair ts  = cpair (us ⧺⊦ ts)
us ⧺⊦ cfst ts   = cfst (us ⧺⊦ ts)
us ⧺⊦ csnd ts   = csnd (us ⧺⊦ ts)
us ⧺⊦ unit ts   = unit (us ⧺⊦ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
app {A} {B} (Ξ , ts) (Ξ′ , us) = Ξ″ , vs
  where Ξ″ = (Ξ′ , A) ⧺ (Ξ , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺₁ (Ξ , A ▻ B)) top) (us ⧺⊦ ts)

box : ∀ {A Γ Δ} → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A
box (Ξ , ts) = ∅ , nec ts nil
