-- Hilbert-style formalisation of syntax.
-- Sequences of terms.

module BasicIS4.Syntax.HilbertSequential where

open import BasicIS4.Syntax.Common public


-- Derivations.

infix 3 _⊦⊢_
data _⊦⊢_ (Γ : Cx Ty) : Cx Ty → Set where
  nil   : Γ ⊦⊢ ⌀
  var   : ∀ {Ξ A}     → A ∈ Γ → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A
  mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , B
  ci    : ∀ {Ξ A}     → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A ▻ A
  ck    : ∀ {Ξ A B}   → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C} → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  nec   : ∀ {Ξ Ψ A}   → ⌀ ⊦⊢ Ψ , A → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , □ A
  cdist : ∀ {Ξ A B}   → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {Ξ A}     → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , □ A ▻ □ □ A
  cdown : ∀ {Ξ A}     → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , □ A ▻ A
  cpair : ∀ {Ξ A B}   → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B}   → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B}   → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , A ∧ B ▻ B
  tt    : ∀ {Ξ}       → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ , ⊤

infix 3 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = ∃ (λ Ξ → Γ ⊦⊢ Ξ , A)


-- Monotonicity with respect to context inclusion.

mono⊦⊢ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊦⊢ Ξ → Γ′ ⊦⊢ Ξ
mono⊦⊢ η nil         = nil
mono⊦⊢ η (var i ts)  = var (mono∈ η i) (mono⊦⊢ η ts)
mono⊦⊢ η (mp i j ts) = mp i j (mono⊦⊢ η ts)
mono⊦⊢ η (ci ts)     = ci (mono⊦⊢ η ts)
mono⊦⊢ η (ck ts)     = ck (mono⊦⊢ η ts)
mono⊦⊢ η (cs ts)     = cs (mono⊦⊢ η ts)
mono⊦⊢ η (nec ss ts) = nec ss (mono⊦⊢ η ts)
mono⊦⊢ η (cdist ts)  = cdist (mono⊦⊢ η ts)
mono⊦⊢ η (cup ts)    = cup (mono⊦⊢ η ts)
mono⊦⊢ η (cdown ts)  = cdown (mono⊦⊢ η ts)
mono⊦⊢ η (cpair ts)  = cpair (mono⊦⊢ η ts)
mono⊦⊢ η (cfst ts)   = cfst (mono⊦⊢ η ts)
mono⊦⊢ η (csnd ts)   = csnd (mono⊦⊢ η ts)
mono⊦⊢ η (tt ts)     = tt (mono⊦⊢ η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Ξ , ts) = Ξ , mono⊦⊢ η ts


-- Derivation concatenation.

_⧺⊦_ : ∀ {Γ Ξ Ξ′} → Γ ⊦⊢ Ξ → Γ ⊦⊢ Ξ′ → Γ ⊦⊢ Ξ ⧺ Ξ′
us ⧺⊦ nil       = us
us ⧺⊦ var i ts  = var i (us ⧺⊦ ts)
us ⧺⊦ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧺⊦ ts)
us ⧺⊦ ci ts     = ci (us ⧺⊦ ts)
us ⧺⊦ ck ts     = ck (us ⧺⊦ ts)
us ⧺⊦ cs ts     = cs (us ⧺⊦ ts)
us ⧺⊦ nec ss ts = nec ss (us ⧺⊦ ts)
us ⧺⊦ cdist ts  = cdist (us ⧺⊦ ts)
us ⧺⊦ cup ts    = cup (us ⧺⊦ ts)
us ⧺⊦ cdown ts  = cdown (us ⧺⊦ ts)
us ⧺⊦ cpair ts  = cpair (us ⧺⊦ ts)
us ⧺⊦ cfst ts   = cfst (us ⧺⊦ ts)
us ⧺⊦ csnd ts   = csnd (us ⧺⊦ ts)
us ⧺⊦ tt ts     = tt (us ⧺⊦ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ▻ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Ξ , ts) (Ξ′ , us) = Ξ″ , vs
  where Ξ″ = (Ξ′ , A) ⧺ (Ξ , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Ξ , A ▻ B)) top) (us ⧺⊦ ts)

box : ∀ {A Γ} → ⌀ ⊢ A → Γ ⊢ □ A
box (Ξ , ts) = ⌀ , nec ts nil
