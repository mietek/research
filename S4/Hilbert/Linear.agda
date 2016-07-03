module S4.Hilbert.Linear where

open import S4.Core public


-- Proofs of S4, as Hilbert-style combinator sequences.

mutual
  infix 1 _⨾_⊢⁺_
  data _⨾_⊢⁺_ (Γ Δ : Cx Ty) : Seq Ty → Set where
    nil  : Γ ⨾ Δ ⊢⁺ []
    var  : ∀ {Π A}     → A ∈ Γ → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π
    mp   : ∀ {Π A B}   → Π ∋ A ⇒ B → Π ∋ A → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ B ∷ Π
    ci   : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ A ∷ Π
    ck   : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ B ⇒ A ∷ Π
    cs   : ∀ {Π A B C} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C ∷ Π
    mvar : ∀ {Π A}     → A ∈ Δ → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π
    nec  : ∀ {Π A}     → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ∷ Π
    dist : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ (A ⇒ B) ⇒ □ A ⇒ □ B ∷ Π
    up   : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ⇒ □ □ A ∷ Π
    down : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ⇒ A ∷ Π
    pair : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ B ⇒ A ∧ B ∷ Π
    fst  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∧ B ⇒ A ∷ Π
    snd  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∧ B ⇒ B ∷ Π
    inl  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ A ∨ B ∷ Π
    inr  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ B ⇒ A ∨ B ∷ Π
    case : ∀ {Π A B C} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C ∷ Π
    boom : ∀ {Π C}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ ⊥ ⇒ C ∷ Π

  infix 1 _⨾_⊢_
  _⨾_⊢_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⨾ Δ ⊢ A = Σ (Seq Ty) (λ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π)


-- Monotonicity of syntactic consequence.

mono⊢⁺ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢⁺ Π → Γ′ ⨾ Δ ⊢⁺ Π
mono⊢⁺ η nil         = nil
mono⊢⁺ η (var i ts)  = var (mono∈ η i) (mono⊢⁺ η ts)
mono⊢⁺ η (mp i j ts) = mp i j (mono⊢⁺ η ts)
mono⊢⁺ η (ci ts)     = ci (mono⊢⁺ η ts)
mono⊢⁺ η (ck ts)     = ck (mono⊢⁺ η ts)
mono⊢⁺ η (cs ts)     = cs (mono⊢⁺ η ts)
mono⊢⁺ η (mvar i ts) = mvar i (mono⊢⁺ η ts)
mono⊢⁺ η (nec ss ts) = nec ss (mono⊢⁺ η ts)
mono⊢⁺ η (dist ts)   = dist (mono⊢⁺ η ts)
mono⊢⁺ η (up ts)     = up (mono⊢⁺ η ts)
mono⊢⁺ η (down ts)   = down (mono⊢⁺ η ts)
mono⊢⁺ η (pair ts)   = pair (mono⊢⁺ η ts)
mono⊢⁺ η (fst ts)    = fst (mono⊢⁺ η ts)
mono⊢⁺ η (snd ts)    = snd (mono⊢⁺ η ts)
mono⊢⁺ η (inl ts)    = inl (mono⊢⁺ η ts)
mono⊢⁺ η (inr ts)    = inr (mono⊢⁺ η ts)
mono⊢⁺ η (case ts)   = case (mono⊢⁺ η ts)
mono⊢⁺ η (boom ts)   = boom (mono⊢⁺ η ts)

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⁺ η ts


-- Modal monotonicity.

mutual
  mmono⊢⁺ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ′ ⊢⁺ Π
  mmono⊢⁺ η nil         = nil
  mmono⊢⁺ η (var i ts)  = var i (mmono⊢⁺ η ts)
  mmono⊢⁺ η (mp i j ts) = mp i j (mmono⊢⁺ η ts)
  mmono⊢⁺ η (ci ts)     = ci (mmono⊢⁺ η ts)
  mmono⊢⁺ η (ck ts)     = ck (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cs ts)     = cs (mmono⊢⁺ η ts)
  mmono⊢⁺ η (mvar i ts) = mvar (mono∈ η i) (mmono⊢⁺ η ts)
  mmono⊢⁺ η (nec ss ts) = nec (mmono⊢ η ss) (mmono⊢⁺ η ts)
  mmono⊢⁺ η (dist ts)   = dist (mmono⊢⁺ η ts)
  mmono⊢⁺ η (up ts)     = up (mmono⊢⁺ η ts)
  mmono⊢⁺ η (down ts)   = down (mmono⊢⁺ η ts)
  mmono⊢⁺ η (pair ts)   = pair (mmono⊢⁺ η ts)
  mmono⊢⁺ η (fst ts)    = fst (mmono⊢⁺ η ts)
  mmono⊢⁺ η (snd ts)    = snd (mmono⊢⁺ η ts)
  mmono⊢⁺ η (inl ts)    = inl (mmono⊢⁺ η ts)
  mmono⊢⁺ η (inr ts)    = inr (mmono⊢⁺ η ts)
  mmono⊢⁺ η (case ts)   = case (mmono⊢⁺ η ts)
  mmono⊢⁺ η (boom ts)   = boom (mmono⊢⁺ η ts)

  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
  mmono⊢ η (Π ∙ ts) = Π ∙ mmono⊢⁺ η ts


-- Proof concatenation.

_++⁺_ : ∀ {Γ Δ Π Π′} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ Π′ → Γ ⨾ Δ ⊢⁺ Π ++ Π′
nil         ++⁺ us = us
(var i ts)  ++⁺ us = var i (ts ++⁺ us)
(mp i j ts) ++⁺ us = mp (mono∋⁺⁺ i) (mono∋⁺⁺ j) (ts ++⁺ us)
(ci ts)     ++⁺ us = ci (ts ++⁺ us)
(ck ts)     ++⁺ us = ck (ts ++⁺ us)
(cs ts)     ++⁺ us = cs (ts ++⁺ us)
(mvar i ts) ++⁺ us = mvar i (ts ++⁺ us)
(nec ss ts) ++⁺ us = nec ss (ts ++⁺ us)
(dist ts)   ++⁺ us = dist (ts ++⁺ us)
(up ts)     ++⁺ us = up (ts ++⁺ us)
(down ts)   ++⁺ us = down (ts ++⁺ us)
(pair ts)   ++⁺ us = pair (ts ++⁺ us)
(fst ts)    ++⁺ us = fst (ts ++⁺ us)
(snd ts)    ++⁺ us = snd (ts ++⁺ us)
(inl ts)    ++⁺ us = inl (ts ++⁺ us)
(inr ts)    ++⁺ us = inr (ts ++⁺ us)
(case ts)   ++⁺ us = case (ts ++⁺ us)
(boom ts)   ++⁺ us = boom (ts ++⁺ us)


-- Modus ponens in expanded form.

app : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (A ⇒ B ∷ Π) ++ (A ∷ Π′) ∙ mp top (mono⁺⁺∋ (A ⇒ B ∷ Π) top) (ts ++⁺ us)
