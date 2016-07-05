module IPC.Hilbert.Linear where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator sequences.

infix 1 _⊢⁺_
data _⊢⁺_ (Γ : Cx Ty) : Seq Ty → Set where
  nil   : Γ ⊢⁺ []
  var   : ∀ {Π A}     → A ∈ Γ → Γ ⊢⁺ Π → Γ ⊢⁺ A ∷ Π
  mp    : ∀ {Π A B}   → Π ∋ A ⇒ B → Π ∋ A → Γ ⊢⁺ Π → Γ ⊢⁺ B ∷ Π
  ci    : ∀ {Π A}     → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ A ∷ Π
  ck    : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ B ⇒ A ∷ Π
  cs    : ∀ {Π A B C} → Γ ⊢⁺ Π → Γ ⊢⁺ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C ∷ Π
  cpair : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ B ⇒ A ∧ B ∷ Π
  cfst  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ∧ B ⇒ A ∷ Π
  csnd  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ∧ B ⇒ B ∷ Π
  cinl  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ A ∨ B ∷ Π
  cinr  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ B ⇒ A ∨ B ∷ Π
  ccase : ∀ {Π A B C} → Γ ⊢⁺ Π → Γ ⊢⁺ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C ∷ Π
  cboom : ∀ {Π C}     → Γ ⊢⁺ Π → Γ ⊢⁺ ⊥ ⇒ C ∷ Π

infix 1 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = Σ (Seq Ty) (λ Π → Γ ⊢⁺ A ∷ Π)


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢⁺ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⁺ Π → Γ′ ⊢⁺ Π
mono⊢⁺ η nil         = nil
mono⊢⁺ η (var i ts)  = var (mono∈ η i) (mono⊢⁺ η ts)
mono⊢⁺ η (mp i j ts) = mp i j (mono⊢⁺ η ts)
mono⊢⁺ η (ci ts)     = ci (mono⊢⁺ η ts)
mono⊢⁺ η (ck ts)     = ck (mono⊢⁺ η ts)
mono⊢⁺ η (cs ts)     = cs (mono⊢⁺ η ts)
mono⊢⁺ η (cpair ts)  = cpair (mono⊢⁺ η ts)
mono⊢⁺ η (cfst ts)   = cfst (mono⊢⁺ η ts)
mono⊢⁺ η (csnd ts)   = csnd (mono⊢⁺ η ts)
mono⊢⁺ η (cinl ts)   = cinl (mono⊢⁺ η ts)
mono⊢⁺ η (cinr ts)   = cinr (mono⊢⁺ η ts)
mono⊢⁺ η (ccase ts)  = ccase (mono⊢⁺ η ts)
mono⊢⁺ η (cboom ts)  = cboom (mono⊢⁺ η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⁺ η ts


-- Proof concatenation.

_++⁺_ : ∀ {Γ Π Π′} → Γ ⊢⁺ Π → Γ ⊢⁺ Π′ → Γ ⊢⁺ Π ∓∓ Π′
nil         ++⁺ us = us
(var i ts)  ++⁺ us = var i (ts ++⁺ us)
(mp i j ts) ++⁺ us = mp (mono∋∓∓ᴸ i) (mono∋∓∓ᴸ j) (ts ++⁺ us)
(ci ts)     ++⁺ us = ci (ts ++⁺ us)
(ck ts)     ++⁺ us = ck (ts ++⁺ us)
(cs ts)     ++⁺ us = cs (ts ++⁺ us)
(cpair ts)  ++⁺ us = cpair (ts ++⁺ us)
(cfst ts)   ++⁺ us = cfst (ts ++⁺ us)
(csnd ts)   ++⁺ us = csnd (ts ++⁺ us)
(cinl ts)   ++⁺ us = cinl (ts ++⁺ us)
(cinr ts)   ++⁺ us = cinr (ts ++⁺ us)
(ccase ts)  ++⁺ us = ccase (ts ++⁺ us)
(cboom ts)  ++⁺ us = cboom (ts ++⁺ us)


-- Modus ponens in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (A ⇒ B ∷ Π) ∓∓ (A ∷ Π′) ∙ mp top (mono∋∓∓ᴿ (A ⇒ B ∷ Π) top) (ts ++⁺ us)
