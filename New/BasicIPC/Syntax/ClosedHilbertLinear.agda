-- Linear Hilbert-style axiomatic formalisation of closed syntax.

module New.BasicIPC.Syntax.ClosedHilbertLinear where

open import New.BasicIPC.Syntax.Common public


-- Derivations.

infix 3 ⊢×_
data ⊢×_ : Cx Ty → Set where
  nil   : ⊢× ⌀
  mp    : ∀ {Π A B}   → A ▻ B ∈ Π → A ∈ Π → ⊢× Π → ⊢× Π , B
  ci    : ∀ {Π A}     → ⊢× Π → ⊢× Π , A ▻ A
  ck    : ∀ {Π A B}   → ⊢× Π → ⊢× Π , A ▻ B ▻ A
  cs    : ∀ {Π A B C} → ⊢× Π → ⊢× Π , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  cpair : ∀ {Π A B}   → ⊢× Π → ⊢× Π , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Π A B}   → ⊢× Π → ⊢× Π , A ∧ B ▻ A
  csnd  : ∀ {Π A B}   → ⊢× Π → ⊢× Π , A ∧ B ▻ B
  tt    : ∀ {Π}       → ⊢× Π → ⊢× Π , ⊤

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Π → ⊢× Π , A)


-- Derivation concatenation.

_⧻_ : ∀ {Π Π′} → ⊢× Π → ⊢× Π′ → ⊢× Π ⧺ Π′
us ⧻ nil       = us
us ⧻ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧻ ts)
us ⧻ ci ts     = ci (us ⧻ ts)
us ⧻ ck ts     = ck (us ⧻ ts)
us ⧻ cs ts     = cs (us ⧻ ts)
us ⧻ cpair ts  = cpair (us ⧻ ts)
us ⧻ cfst ts   = cfst (us ⧻ ts)
us ⧻ csnd ts   = csnd (us ⧻ ts)
us ⧻ tt ts     = tt (us ⧻ ts)


-- Modus ponens in expanded form.

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Π , ts) (Π′ , us) = Π″ , vs
  where Π″ = (Π′ , A) ⧺ (Π , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Π , A ▻ B)) top) (us ⧻ ts)
