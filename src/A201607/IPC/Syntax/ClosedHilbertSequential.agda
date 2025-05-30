{-# OPTIONS --sized-types #-}

-- Intuitionistic propositional calculus.
-- Hilbert-style formalisation of closed syntax.
-- Sequences of terms.

module A201607.IPC.Syntax.ClosedHilbertSequential where

open import A201607.IPC.Syntax.Common public


-- Derivations.

infix 3 ⊦⊢_
data ⊦⊢_ : Cx Ty → Set where
  nil   : ⊦⊢ ∅
  mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊦⊢ Ξ → ⊦⊢ Ξ , B
  ci    : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ A
  ck    : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C} → ⊦⊢ Ξ → ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  cpair : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ B
  unit  : ∀ {Ξ}       → ⊦⊢ Ξ → ⊦⊢ Ξ , ⊤
  cboom : ∀ {Ξ C}     → ⊦⊢ Ξ → ⊦⊢ Ξ , ⊥ ▻ C
  cinl  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ A ∨ B
  cinr  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , B ▻ A ∨ B
  ccase : ∀ {Ξ A B C} → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∨ B ▻ (A ▻ C) ▻ (B ▻ C) ▻ C

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊦⊢ Ξ , A)


-- Concatenation of derivations.

_⧺⊦_ : ∀ {Ξ Ξ′} → ⊦⊢ Ξ → ⊦⊢ Ξ′ → ⊦⊢ Ξ ⧺ Ξ′
us ⧺⊦ nil       = us
us ⧺⊦ mp i j ts = mp (mono∈ weak⊆⧺₂ i) (mono∈ weak⊆⧺₂ j) (us ⧺⊦ ts)
us ⧺⊦ ci ts     = ci (us ⧺⊦ ts)
us ⧺⊦ ck ts     = ck (us ⧺⊦ ts)
us ⧺⊦ cs ts     = cs (us ⧺⊦ ts)
us ⧺⊦ cpair ts  = cpair (us ⧺⊦ ts)
us ⧺⊦ cfst ts   = cfst (us ⧺⊦ ts)
us ⧺⊦ csnd ts   = csnd (us ⧺⊦ ts)
us ⧺⊦ unit ts   = unit (us ⧺⊦ ts)
us ⧺⊦ cboom ts  = cboom (us ⧺⊦ ts)
us ⧺⊦ cinl ts   = cinl (us ⧺⊦ ts)
us ⧺⊦ cinr ts   = cinr (us ⧺⊦ ts)
us ⧺⊦ ccase ts  = ccase (us ⧺⊦ ts)


-- Modus ponens in expanded form.

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Ξ , ts) (Ξ′ , us) = Ξ″ , vs
  where Ξ″ = (Ξ′ , A) ⧺ (Ξ , A ▻ B)
        vs = mp top (mono∈ (weak⊆⧺₁ (Ξ , A ▻ B)) top) (us ⧺⊦ ts)
