module IPC.Hilbert.List where

open import IPC public


-- Derivations, as Hilbert-style lists of combinators.

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
  cboom : ∀ {Π C}     → ⊢× Π → ⊢× Π , ⊥ ▻ C
  cinl  : ∀ {Π A B}   → ⊢× Π → ⊢× Π , A ▻ A ∨ B
  cinr  : ∀ {Π A B}   → ⊢× Π → ⊢× Π , B ▻ A ∨ B
  ccase : ∀ {Π A B C} → ⊢× Π → ⊢× Π , A ∨ B ▻ (A ▻ C) ▻ (B ▻ C) ▻ C

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
us ⧻ cboom ts  = cboom (us ⧻ ts)
us ⧻ cinl ts   = cinl (us ⧻ ts)
us ⧻ cinr ts   = cinr (us ⧻ ts)
us ⧻ ccase ts  = ccase (us ⧻ ts)


-- Modus ponens in expanded form.

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Π , ts) (Π′ , us) = Π″ , vs
  where Π″ = (Π′ , A) ⧺ (Π , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Π , A ▻ B)) top) (us ⧻ ts)
