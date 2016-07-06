module IPC.Hilbert.Linear where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator sequences.

infix 1 _⊢⋆_
data _⊢⋆_ (Γ : Cx Ty) : Seq Ty → Set where
  nil   : Γ ⊢⋆ []
  var   : ∀ {Π A}     → A ∈ Γ → Γ ⊢⋆ Π → Γ ⊢⋆ A ∷ Π
  mp    : ∀ {Π A B}   → Π ∋ A ⊃ B → Π ∋ A → Γ ⊢⋆ Π → Γ ⊢⋆ B ∷ Π
  ci    : ∀ {Π A}     → Γ ⊢⋆ Π → Γ ⊢⋆ A ⊃ A ∷ Π
  ck    : ∀ {Π A B}   → Γ ⊢⋆ Π → Γ ⊢⋆ A ⊃ B ⊃ A ∷ Π
  cs    : ∀ {Π A B C} → Γ ⊢⋆ Π → Γ ⊢⋆ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C ∷ Π
  unit  : ∀ {Π}       → Γ ⊢⋆ Π → Γ ⊢⋆ ι ∷ Π
  cpair : ∀ {Π A B}   → Γ ⊢⋆ Π → Γ ⊢⋆ A ⊃ B ⊃ A ∧ B ∷ Π
  cfst  : ∀ {Π A B}   → Γ ⊢⋆ Π → Γ ⊢⋆ A ∧ B ⊃ A ∷ Π
  csnd  : ∀ {Π A B}   → Γ ⊢⋆ Π → Γ ⊢⋆ A ∧ B ⊃ B ∷ Π

infix 1 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = Σ (Seq Ty) (λ Π → Γ ⊢⋆ A ∷ Π)


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Π → Γ′ ⊢⋆ Π
mono⊢⋆ η nil         = nil
mono⊢⋆ η (var i ts)  = var (mono∈ η i) (mono⊢⋆ η ts)
mono⊢⋆ η (mp i j ts) = mp i j (mono⊢⋆ η ts)
mono⊢⋆ η (ci ts)     = ci (mono⊢⋆ η ts)
mono⊢⋆ η (ck ts)     = ck (mono⊢⋆ η ts)
mono⊢⋆ η (cs ts)     = cs (mono⊢⋆ η ts)
mono⊢⋆ η (unit ts)   = unit (mono⊢⋆ η ts)
mono⊢⋆ η (cpair ts)  = cpair (mono⊢⋆ η ts)
mono⊢⋆ η (cfst ts)   = cfst (mono⊢⋆ η ts)
mono⊢⋆ η (csnd ts)   = csnd (mono⊢⋆ η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⋆ η ts


-- Proof concatenation.

_⧺⋆_ : ∀ {Γ Π Π′} → Γ ⊢⋆ Π → Γ ⊢⋆ Π′ → Γ ⊢⋆ Π ⧺ₛ Π′
nil         ⧺⋆ us = us
(var i ts)  ⧺⋆ us = var i (ts ⧺⋆ us)
(mp i j ts) ⧺⋆ us = mp (mono∋ i) (mono∋ j) (ts ⧺⋆ us)
(ci ts)     ⧺⋆ us = ci (ts ⧺⋆ us)
(ck ts)     ⧺⋆ us = ck (ts ⧺⋆ us)
(cs ts)     ⧺⋆ us = cs (ts ⧺⋆ us)
(unit ts)   ⧺⋆ us = unit (ts ⧺⋆ us)
(cpair ts)  ⧺⋆ us = cpair (ts ⧺⋆ us)
(cfst ts)   ⧺⋆ us = cfst (ts ⧺⋆ us)
(csnd ts)   ⧺⋆ us = csnd (ts ⧺⋆ us)


-- Modus ponens in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (A ⊃ B ∷ Π) ⧺ₛ (A ∷ Π′) ∙ mp top (mono∋′ (A ⊃ B ∷ Π) top) (ts ⧺⋆ us)
