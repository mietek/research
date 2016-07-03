module IPC.Hilbert.Linear where

open import IPC.Core public


-- Proofs of IPC, as Hilbert-style combinator sequences.

infix 1 _⊢⁺_
data _⊢⁺_ (Γ : Cx Ty) : Seq Ty → Set where
  nil  : Γ ⊢⁺ []
  var  : ∀ {Π A}     → A ∈ Γ → Γ ⊢⁺ Π → Γ ⊢⁺ A ∷ Π
  mp   : ∀ {Π A B}   → Π ∋ A ⇒ B → Π ∋ A → Γ ⊢⁺ Π → Γ ⊢⁺ B ∷ Π
  ci   : ∀ {Π A}     → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ A ∷ Π
  ck   : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ B ⇒ A ∷ Π
  cs   : ∀ {Π A B C} → Γ ⊢⁺ Π → Γ ⊢⁺ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C ∷ Π
  pair : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ B ⇒ A ∧ B ∷ Π
  fst  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ∧ B ⇒ A ∷ Π
  snd  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ∧ B ⇒ B ∷ Π
  inl  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ A ⇒ A ∨ B ∷ Π
  inr  : ∀ {Π A B}   → Γ ⊢⁺ Π → Γ ⊢⁺ B ⇒ A ∨ B ∷ Π
  case : ∀ {Π A B C} → Γ ⊢⁺ Π → Γ ⊢⁺ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C ∷ Π
  boom : ∀ {Π C}     → Γ ⊢⁺ Π → Γ ⊢⁺ ⊥ ⇒ C ∷ Π

infix 1 _⊢_
_⊢_ : Cx Ty → Ty → Set
Γ ⊢ A = Σ (Seq Ty) (λ Π → Γ ⊢⁺ A ∷ Π)


-- Monotonicity of syntactic consequence.

mono⊢⁺ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⁺ Π → Γ′ ⊢⁺ Π
mono⊢⁺ η nil         = nil
mono⊢⁺ η (var i ts)  = var (mono∈ η i) (mono⊢⁺ η ts)
mono⊢⁺ η (mp i j ts) = mp i j (mono⊢⁺ η ts)
mono⊢⁺ η (ci ts)     = ci (mono⊢⁺ η ts)
mono⊢⁺ η (ck ts)     = ck (mono⊢⁺ η ts)
mono⊢⁺ η (cs ts)     = cs (mono⊢⁺ η ts)
mono⊢⁺ η (pair ts)   = pair (mono⊢⁺ η ts)
mono⊢⁺ η (fst ts)    = fst (mono⊢⁺ η ts)
mono⊢⁺ η (snd ts)    = snd (mono⊢⁺ η ts)
mono⊢⁺ η (inl ts)    = inl (mono⊢⁺ η ts)
mono⊢⁺ η (inr ts)    = inr (mono⊢⁺ η ts)
mono⊢⁺ η (case ts)   = case (mono⊢⁺ η ts)
mono⊢⁺ η (boom ts)   = boom (mono⊢⁺ η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⁺ η ts


-- Proof concatenation.

_++⁺_ : ∀ {Γ Π Π′} → Γ ⊢⁺ Π → Γ ⊢⁺ Π′ → Γ ⊢⁺ Π ++ Π′
nil         ++⁺ us = us
(var i ts)  ++⁺ us = var i (ts ++⁺ us)
(mp i j ts) ++⁺ us = mp (mono∋⁺⁺ i) (mono∋⁺⁺ j) (ts ++⁺ us)
(ci ts)     ++⁺ us = ci (ts ++⁺ us)
(ck ts)     ++⁺ us = ck (ts ++⁺ us)
(cs ts)     ++⁺ us = cs (ts ++⁺ us)
(pair ts)   ++⁺ us = pair (ts ++⁺ us)
(fst ts)    ++⁺ us = fst (ts ++⁺ us)
(snd ts)    ++⁺ us = snd (ts ++⁺ us)
(inl ts)    ++⁺ us = inl (ts ++⁺ us)
(inr ts)    ++⁺ us = inr (ts ++⁺ us)
(case ts)   ++⁺ us = case (ts ++⁺ us)
(boom ts)   ++⁺ us = boom (ts ++⁺ us)


-- Modus ponens in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (A ⇒ B ∷ Π) ++ (A ∷ Π′) ∙ mp top (mono⁺⁺∋ (A ⇒ B ∷ Π) top) (ts ++⁺ us)
