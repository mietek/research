module S4.Hilbert.Linear where

open import S4.Core public


-- Proofs of S4, as Hilbert-style combinator sequences.

mutual
  infix 1 _⨾_⊢⁺_
  data _⨾_⊢⁺_ (Γ Δ : Cx Ty) : Seq Ty → Set where
    nil   : Γ ⨾ Δ ⊢⁺ []
    var   : ∀ {Π A}     → A ∈ Γ → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π
    mp    : ∀ {Π A B}   → Π ∋ A ⇒ B → Π ∋ A → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ B ∷ Π
    ci    : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ A ∷ Π
    ck    : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ B ⇒ A ∷ Π
    cs    : ∀ {Π A B C} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C ∷ Π
    mvar  : ∀ {Π A}     → A ∈ Δ → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π
    nec   : ∀ {Π A}     → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ∷ Π
    cdist : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ (A ⇒ B) ⇒ □ A ⇒ □ B ∷ Π
    cup   : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ⇒ □ □ A ∷ Π
    cdown : ∀ {Π A}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ □ A ⇒ A ∷ Π
    unit  : ∀ {Π}       → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ ⊤ ∷ Π
    cpair : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ B ⇒ A ∧ B ∷ Π
    cfst  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∧ B ⇒ A ∷ Π
    csnd  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∧ B ⇒ B ∷ Π
    cinl  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ⇒ A ∨ B ∷ Π
    cinr  : ∀ {Π A B}   → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ B ⇒ A ∨ B ∷ Π
    ccase : ∀ {Π A B C} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C ∷ Π
    cboom : ∀ {Π C}     → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ ⊥ ⇒ C ∷ Π

  infix 1 _⨾_⊢_
  _⨾_⊢_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⨾ Δ ⊢ A = Σ (Seq Ty) (λ Π → Γ ⨾ Δ ⊢⁺ A ∷ Π)


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢⁺ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢⁺ Π → Γ′ ⨾ Δ ⊢⁺ Π
mono⊢⁺ η nil         = nil
mono⊢⁺ η (var i ts)  = var (mono∈ η i) (mono⊢⁺ η ts)
mono⊢⁺ η (mp i j ts) = mp i j (mono⊢⁺ η ts)
mono⊢⁺ η (ci ts)     = ci (mono⊢⁺ η ts)
mono⊢⁺ η (ck ts)     = ck (mono⊢⁺ η ts)
mono⊢⁺ η (cs ts)     = cs (mono⊢⁺ η ts)
mono⊢⁺ η (mvar i ts) = mvar i (mono⊢⁺ η ts)
mono⊢⁺ η (nec ss ts) = nec ss (mono⊢⁺ η ts)
mono⊢⁺ η (cdist ts)  = cdist (mono⊢⁺ η ts)
mono⊢⁺ η (cup ts)    = cup (mono⊢⁺ η ts)
mono⊢⁺ η (cdown ts)  = cdown (mono⊢⁺ η ts)
mono⊢⁺ η (unit ts)   = unit (mono⊢⁺ η ts)
mono⊢⁺ η (cpair ts)  = cpair (mono⊢⁺ η ts)
mono⊢⁺ η (cfst ts)   = cfst (mono⊢⁺ η ts)
mono⊢⁺ η (csnd ts)   = csnd (mono⊢⁺ η ts)
mono⊢⁺ η (cinl ts)   = cinl (mono⊢⁺ η ts)
mono⊢⁺ η (cinr ts)   = cinr (mono⊢⁺ η ts)
mono⊢⁺ η (ccase ts)  = ccase (mono⊢⁺ η ts)
mono⊢⁺ η (cboom ts)  = cboom (mono⊢⁺ η ts)

mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⨾ Δ ⊢ A → Γ′ ⨾ Δ ⊢ A
mono⊢ η (Π ∙ ts) = Π ∙ mono⊢⁺ η ts


-- Monotonicity of syntactic consequence with respect to modal context extension.

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
  mmono⊢⁺ η (cdist ts)  = cdist (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cup ts)    = cup (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cdown ts)  = cdown (mmono⊢⁺ η ts)
  mmono⊢⁺ η (unit ts)   = unit (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cpair ts)  = cpair (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cfst ts)   = cfst (mmono⊢⁺ η ts)
  mmono⊢⁺ η (csnd ts)   = csnd (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cinl ts)   = cinl (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cinr ts)   = cinr (mmono⊢⁺ η ts)
  mmono⊢⁺ η (ccase ts)  = ccase (mmono⊢⁺ η ts)
  mmono⊢⁺ η (cboom ts)  = cboom (mmono⊢⁺ η ts)

  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ′ ⊢ A
  mmono⊢ η (Π ∙ ts) = Π ∙ mmono⊢⁺ η ts


-- Proof concatenation.

_++⁺_ : ∀ {Γ Δ Π Π′} → Γ ⨾ Δ ⊢⁺ Π → Γ ⨾ Δ ⊢⁺ Π′ → Γ ⨾ Δ ⊢⁺ Π ∓∓ Π′
nil         ++⁺ us = us
(var i ts)  ++⁺ us = var i (ts ++⁺ us)
(mp i j ts) ++⁺ us = mp (mono∋∓∓ᴸ i) (mono∋∓∓ᴸ j) (ts ++⁺ us)
(ci ts)     ++⁺ us = ci (ts ++⁺ us)
(ck ts)     ++⁺ us = ck (ts ++⁺ us)
(cs ts)     ++⁺ us = cs (ts ++⁺ us)
(mvar i ts) ++⁺ us = mvar i (ts ++⁺ us)
(nec ss ts) ++⁺ us = nec ss (ts ++⁺ us)
(cdist ts)  ++⁺ us = cdist (ts ++⁺ us)
(cup ts)    ++⁺ us = cup (ts ++⁺ us)
(cdown ts)  ++⁺ us = cdown (ts ++⁺ us)
(unit ts)   ++⁺ us = unit (ts ++⁺ us)
(cpair ts)  ++⁺ us = cpair (ts ++⁺ us)
(cfst ts)   ++⁺ us = cfst (ts ++⁺ us)
(csnd ts)   ++⁺ us = csnd (ts ++⁺ us)
(cinl ts)   ++⁺ us = cinl (ts ++⁺ us)
(cinr ts)   ++⁺ us = cinr (ts ++⁺ us)
(ccase ts)  ++⁺ us = ccase (ts ++⁺ us)
(cboom ts)  ++⁺ us = cboom (ts ++⁺ us)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ Δ} → Γ ⨾ Δ ⊢ A ⇒ B → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ B
app {A} {B} (Π ∙ ts) (Π′ ∙ us) =
    (A ⇒ B ∷ Π) ∓∓ (A ∷ Π′) ∙ mp top (mono∋∓∓ᴿ (A ⇒ B ∷ Π) top) (ts ++⁺ us)

box : ∀ {A Γ Δ} → ∅ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ □ A
box ts = [] ∙ nec ts nil
