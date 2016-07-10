module IPC.Hilbert.Linear where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator sequences.

infix 1 _⊢ₛ_
data _⊢ₛ_ (Γ : Cx Ty) : Cx Ty → Set where
  nil   : Γ ⊢ₛ ⌀
  var   : ∀ {Π A}     → A ∈ Γ → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A
  mp    : ∀ {Π A B}   → A ⊃ B ∈ Π → A ∈ Π → Γ ⊢ₛ Π → Γ ⊢ₛ Π , B
  ci    : ∀ {Π A}     → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A ⊃ A
  ck    : ∀ {Π A B}   → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A ⊃ B ⊃ A
  cs    : ∀ {Π A B C} → Γ ⊢ₛ Π → Γ ⊢ₛ Π , (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  unit  : ∀ {Π}       → Γ ⊢ₛ Π → Γ ⊢ₛ Π , ι
  cpair : ∀ {Π A B}   → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A ⊃ B ⊃ A ∧ B
  cfst  : ∀ {Π A B}   → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A ∧ B ⊃ A
  csnd  : ∀ {Π A B}   → Γ ⊢ₛ Π → Γ ⊢ₛ Π , A ∧ B ⊃ B

infix 1 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = Σ (Cx Ty) (λ Π → Γ ⊢ₛ Π , A)


-- Monotonicity of syntactic consequence with respect to context inclusion.

mono⊢ₛ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ₛ Π → Γ′ ⊢ₛ Π
mono⊢ₛ η nil         = nil
mono⊢ₛ η (var i ts)  = var (mono∈ η i) (mono⊢ₛ η ts)
mono⊢ₛ η (mp i j ts) = mp i j (mono⊢ₛ η ts)
mono⊢ₛ η (ci ts)     = ci (mono⊢ₛ η ts)
mono⊢ₛ η (ck ts)     = ck (mono⊢ₛ η ts)
mono⊢ₛ η (cs ts)     = cs (mono⊢ₛ η ts)
mono⊢ₛ η (unit ts)   = unit (mono⊢ₛ η ts)
mono⊢ₛ η (cpair ts)  = cpair (mono⊢ₛ η ts)
mono⊢ₛ η (cfst ts)   = cfst (mono⊢ₛ η ts)
mono⊢ₛ η (csnd ts)   = csnd (mono⊢ₛ η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢ₛ η ts


-- Proof concatenation.

_⧺ₛ_ : ∀ {Γ Π Π′} → Γ ⊢ₛ Π → Γ ⊢ₛ Π′ → Γ ⊢ₛ Π ⧺ Π′
us ⧺ₛ nil       = us
us ⧺ₛ var i ts  = var i (us ⧺ₛ ts)
us ⧺ₛ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧺ₛ ts)
us ⧺ₛ ci ts     = ci (us ⧺ₛ ts)
us ⧺ₛ ck ts     = ck (us ⧺ₛ ts)
us ⧺ₛ cs ts     = cs (us ⧺ₛ ts)
us ⧺ₛ unit ts   = unit (us ⧺ₛ ts)
us ⧺ₛ cpair ts  = cpair (us ⧺ₛ ts)
us ⧺ₛ cfst ts   = cfst (us ⧺ₛ ts)
us ⧺ₛ csnd ts   = csnd (us ⧺ₛ ts)


-- Modus ponens in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (Π′ , A) ⧺ (Π , A ⊃ B) ∙ mp top (mono∈ (weak⊆⧺ₗ (Π , A ⊃ B)) top) (us ⧺ₛ ts)
