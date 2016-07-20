module BasicILP.Indirect.Hilbert.Sequential where

open import BasicILP.Indirect public


-- Derivations, as Hilbert-style combinator sequences.

mutual
  data Tm× : Set where
    NIL   : Tm×
    VAR   : ℕ → Tm× → Tm×
    MP    : ℕ → ℕ → Tm× → Tm×
    CI    : Tm× → Tm×
    CK    : Tm× → Tm×
    CS    : Tm× → Tm×
    NEC   : Tm× → Tm× → Tm×
    CDIST : Tm× → Tm×
    CUP   : Tm× → Tm×
    CDOWN : Tm× → Tm×
    CPAIR : Tm× → Tm×
    CFST  : Tm× → Tm×
    CSND  : Tm× → Tm×
    TT    : Tm× → Tm×

  _[⧻]_ : Tm× → Tm× → Tm×
  [us] [⧻] NIL             = [us]
  [us] [⧻] VAR [i] [ts]    = VAR [i] ([us] [⧻] [ts])
  [us] [⧻] MP [i] [j] [ts] = MP [i] [j] ([us] [⧻] [ts])
  [us] [⧻] CI [ts]         = CI ([us] [⧻] [ts])
  [us] [⧻] CK [ts]         = CK ([us] [⧻] [ts])
  [us] [⧻] CS [ts]         = CS ([us] [⧻] [ts])
  [us] [⧻] NEC [ss] [ts]   = NEC [ss] ([us] [⧻] [ts])
  [us] [⧻] CDIST [ts]      = CDIST ([us] [⧻] [ts])
  [us] [⧻] CUP [ts]        = CUP ([us] [⧻] [ts])
  [us] [⧻] CDOWN [ts]      = CDOWN ([us] [⧻] [ts])
  [us] [⧻] CPAIR [ts]      = CPAIR ([us] [⧻] [ts])
  [us] [⧻] CFST [ts]       = CFST ([us] [⧻] [ts])
  [us] [⧻] CSND [ts]       = CSND ([us] [⧻] [ts])
  [us] [⧻] TT [ts]         = TT ([us] [⧻] [ts])

  infix 3 _⊢×_
  data _⊢×_ (Γ : Cx (Ty Tm×)) : Cx (Ty Tm×) → Set where
    nil   : Γ ⊢× ⌀
    var   : ∀ {Π A}             → A ∈ Γ → Γ ⊢× Π → Γ ⊢× Π , A
    mp    : ∀ {Π A B}           → A ▷ B ∈ Π → A ∈ Π → Γ ⊢× Π → Γ ⊢× Π , B
    ci    : ∀ {Π A}             → Γ ⊢× Π → Γ ⊢× Π , A ▷ A
    ck    : ∀ {Π A B}           → Γ ⊢× Π → Γ ⊢× Π , A ▷ B ▷ A
    cs    : ∀ {Π A B C}         → Γ ⊢× Π → Γ ⊢× Π , (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C

    nec   : ∀ {Π Ξ A}           → (ss : ⌀ ⊢× Ξ , A)
                                → Γ ⊢× Π → Γ ⊢× Π , [ ss ]× ⦂ A
    cdist : ∀ {Π A B [ts] [us]} → Γ ⊢× Π
                                → Γ ⊢× Π , [ts] ⦂ (A ▷ B) ▷ [us] ⦂ A ▷ MP 0 0 {!!} ⦂ B
    cup   : ∀ {Π A [ss]}        → (ts : Γ ⊢× Π)
                                → Γ ⊢× Π , [ss] ⦂ A ▷ NEC [ss] {!!} ⦂ [ss] ⦂ A
    cdown : ∀ {Π A [ss]}        → Γ ⊢× Π
                                → Γ ⊢× Π , [ss] ⦂ A ▷ A

    cpair : ∀ {Π A B}           → Γ ⊢× Π → Γ ⊢× Π , A ▷ B ▷ A ∧ B
    cfst  : ∀ {Π A B}           → Γ ⊢× Π → Γ ⊢× Π , A ∧ B ▷ A
    csnd  : ∀ {Π A B}           → Γ ⊢× Π → Γ ⊢× Π , A ∧ B ▷ B
    tt    : ∀ {Π}               → Γ ⊢× Π → Γ ⊢× Π , ⊤

  [_]× : ∀ {Π Γ} → Γ ⊢× Π → Tm×
  [ nil ]×       = NIL
  [ var i ts ]×  = VAR (ix i) [ ts ]×
  [ mp i j ts ]× = MP (ix i) (ix j) [ ts ]×
  [ ci ts ]×     = CI [ ts ]×
  [ ck ts ]×     = CK [ ts ]×
  [ cs ts ]×     = CS [ ts ]×
  [ nec ss ts ]× = NEC [ ss ]× [ ts ]×
  [ cdist ts ]×  = CDIST [ ts ]×
  [ cup ts ]×    = CUP [ ts ]×
  [ cdown ts ]×  = CDOWN [ ts ]×
  [ cpair ts ]×  = CPAIR [ ts ]×
  [ cfst ts ]×   = CFST [ ts ]×
  [ csnd ts ]×   = CSND [ ts ]×
  [ tt ts ]×     = TT [ ts ]×

infix 3 _⊢_
_⊢_ : Cx (Ty Tm×) → Ty Tm× → Set
Γ ⊢ A = ∃ (λ Π → Γ ⊢× Π , A)

[_] : ∀ {A Γ} → Γ ⊢ A → Tm×
[ Π , ts ] = [ ts ]×


-- Monotonicity with respect to context inclusion.

mono⊢× : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢× Π → Γ′ ⊢× Π
mono⊢× η nil         = nil
mono⊢× η (var i ts)  = var (mono∈ η i) (mono⊢× η ts)
mono⊢× η (mp i j ts) = mp i j (mono⊢× η ts)
mono⊢× η (ci ts)     = ci (mono⊢× η ts)
mono⊢× η (ck ts)     = ck (mono⊢× η ts)
mono⊢× η (cs ts)     = cs (mono⊢× η ts)
mono⊢× η (nec ss ts) = nec ss (mono⊢× η ts)
mono⊢× η (cdist ts)  = cdist (mono⊢× η ts)
mono⊢× η (cup ts)    = {!cup (mono⊢× η ts)!}
mono⊢× η (cdown ts)  = cdown (mono⊢× η ts)
mono⊢× η (cpair ts)  = cpair (mono⊢× η ts)
mono⊢× η (cfst ts)   = cfst (mono⊢× η ts)
mono⊢× η (csnd ts)   = csnd (mono⊢× η ts)
mono⊢× η (tt ts)     = tt (mono⊢× η ts)

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (Π , ts) = Π , mono⊢× η ts


-- Derivation concatenation.

_⧻_ : ∀ {Γ Π Π′} → Γ ⊢× Π → Γ ⊢× Π′ → Γ ⊢× Π ⧺ Π′
us ⧻ nil       = us
us ⧻ var i ts  = var i (us ⧻ ts)
us ⧻ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧻ ts)
us ⧻ ci ts     = ci (us ⧻ ts)
us ⧻ ck ts     = ck (us ⧻ ts)
us ⧻ cs ts     = cs (us ⧻ ts)
us ⧻ nec ss ts = nec ss (us ⧻ ts)
us ⧻ cdist ts  = cdist (us ⧻ ts)
us ⧻ cup ts    = {!cup (us ⧻ ts)!}
us ⧻ cdown ts  = cdown (us ⧻ ts)
us ⧻ cpair ts  = cpair (us ⧻ ts)
us ⧻ cfst ts   = cfst (us ⧻ ts)
us ⧻ csnd ts   = csnd (us ⧻ ts)
us ⧻ tt ts     = tt (us ⧻ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B Γ} → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
app {A} {B} (Π , ts) (Π′ , us) = Π″ , vs
  where Π″ = (Π′ , A) ⧺ (Π , A ▷ B)
        vs = mp top (mono∈ (weak⊆⧺ₗ (Π , A ▷ B)) top) (us ⧻ ts)

box : ∀ {A Γ} → (t : ⌀ ⊢ A) → Γ ⊢ [ t ] ⦂ A
box (Π , ts) = ⌀ , nec ts nil
