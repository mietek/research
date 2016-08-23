-- Hilbert-style formalisation of closed syntax.
-- Sequences of terms.

module BasicIS4.Syntax.ClosedHilbertSequential where

open import BasicIS4.Syntax.Common public


-- Derivations.

infix 3 ⊦⊢_
data ⊦⊢_ : Cx Ty → Set where
  nil   : ⊦⊢ ⌀
  mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊦⊢ Ξ → ⊦⊢ Ξ , B
  ci    : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ A
  ck    : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C} → ⊦⊢ Ξ → ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  nec   : ∀ {Ξ Ξ′ A}  → ⊦⊢ Ξ′ , A → ⊦⊢ Ξ → ⊦⊢ Ξ , □ A
  cdist : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , □ (A ▻ B) ▻ □ A ▻ □ B
  cup   : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , □ A ▻ □ □ A
  cdown : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , □ A ▻ A
  cpair : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ B
  tt    : ∀ {Ξ}       → ⊦⊢ Ξ → ⊦⊢ Ξ , ⊤

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊦⊢ Ξ , A)


-- Derivation concatenation.

_⧺⊦_ : ∀ {Ξ Ξ′} → ⊦⊢ Ξ → ⊦⊢ Ξ′ → ⊦⊢ Ξ ⧺ Ξ′
us ⧺⊦ nil       = us
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

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Ξ , ts) (Ξ′ , us) = Ξ″ , vs
  where Ξ″ = (Ξ′ , A) ⧺ (Ξ , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Ξ , A ▻ B)) top) (us ⧺⊦ ts)

box : ∀ {A} → ⊢ A → ⊢ □ A
box (Ξ , ts) = ⌀ , nec ts nil
