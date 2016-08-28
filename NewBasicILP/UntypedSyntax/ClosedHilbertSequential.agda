module NewBasicILP.UntypedSyntax.ClosedHilbertSequential where

open import NewBasicILP.UntypedSyntax.Common public


-- Untyped representation of derivations.

data Reps : ℕ → Set where
  NIL   : Reps zero
  MP    : ∀ {n} → Fin n → Fin n → Reps n → Reps (suc n)
  CI    : ∀ {n} → Reps n → Reps (suc n)
  CK    : ∀ {n} → Reps n → Reps (suc n)
  CS    : ∀ {n} → Reps n → Reps (suc n)
  NEC   : ∀ {n} → ∀ {`n} → Reps (suc `n) → Reps n → Reps (suc n)
  CDIST : ∀ {n} → Reps n → Reps (suc n)
  CUP   : ∀ {n} → Reps n → Reps (suc n)
  CDOWN : ∀ {n} → Reps n → Reps (suc n)
  CPAIR : ∀ {n} → Reps n → Reps (suc n)
  CFST  : ∀ {n} → Reps n → Reps (suc n)
  CSND  : ∀ {n} → Reps n → Reps (suc n)
  TT    : ∀ {n} → Reps n → Reps (suc n)

Rep : Set
Rep = ∃ (λ n → Reps (suc n))

open ClosedSyntax (Rep) public


-- Concatenation of derivation representations.

_+⊦_ : ∀ {n n′} → Reps n → Reps n′ → Reps (n + n′)
us +⊦ NIL       = us
us +⊦ MP i j ts = MP (monoFin weak≤+ᵣ i) (monoFin weak≤+ᵣ j) (us +⊦ ts)
us +⊦ CI ts     = CI (us +⊦ ts)
us +⊦ CK ts     = CK (us +⊦ ts)
us +⊦ CS ts     = CS (us +⊦ ts)
us +⊦ NEC ps ts = NEC ps (us +⊦ ts)
us +⊦ CDIST ts  = CDIST (us +⊦ ts)
us +⊦ CUP ts    = CUP (us +⊦ ts)
us +⊦ CDOWN ts  = CDOWN (us +⊦ ts)
us +⊦ CPAIR ts  = CPAIR (us +⊦ ts)
us +⊦ CFST ts   = CFST (us +⊦ ts)
us +⊦ CSND ts   = CSND (us +⊦ ts)
us +⊦ TT ts     = TT (us +⊦ ts)


-- TODO

APPS : ∀ {n n′} → Reps (suc n) → Reps (suc n′) → Reps (suc (suc n′ + suc n))
APPS {n} ts us = MP zero (monoFin (weak≤+ₗ (suc n)) zero) (us +⊦ ts)

BOXS : ∀ {n} → Reps (suc n) → Reps (suc zero)
BOXS {n} ps = NEC ps NIL

APP : Rep → Rep → Rep
APP (n , ts) (n′ , us) = suc n′ + suc n , APPS ts us

BOX : Rep → Rep
BOX (n , ps) = zero , BOXS ps


-- Derivations.

mutual
  infix 3 ⊦⊢_
  data ⊦⊢_ : Cx Ty → Set where
    nil   : ⊦⊢ ⌀
    mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊦⊢ Ξ → ⊦⊢ Ξ , B
    ci    : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ A
    ck    : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A
    cs    : ∀ {Ξ A B C} → ⊦⊢ Ξ → ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    nec   : ∀ {Ξ A}     → ∀ {`Ξ} → (ps : ⊦⊢ `Ξ , A)
                        → ⊦⊢ Ξ → ⊦⊢ Ξ , [ REP ps ] A

    cdist : ∀ {Ξ A B}   → ∀ {ps qs}
                        → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] (A ▻ B) ▻ [ qs ] A ▻ [ APP ps qs ] B

    cup   : ∀ {Ξ A}     → ∀ {ps}
                        → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] A ▻ [ BOX ps ] [ ps ] A

    cdown : ∀ {Ξ A}     → ∀ {ps}
                        → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] A ▻ A

    cpair : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
    cfst  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ A
    csnd  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ B
    tt    : ∀ {Ξ}       → ⊦⊢ Ξ → ⊦⊢ Ξ , ⊤

  ᴿ⌊_⌋ : ∀ {Ξ} → ⊦⊢ Ξ → Reps ᴺ⌊ Ξ ⌋
  ᴿ⌊ nil ⌋       = NIL
  ᴿ⌊ mp i j ts ⌋ = MP ⁱ⌊ i ⌋ ⁱ⌊ j ⌋ ᴿ⌊ ts ⌋
  ᴿ⌊ ci ts ⌋     = CI ᴿ⌊ ts ⌋
  ᴿ⌊ ck ts ⌋     = CK ᴿ⌊ ts ⌋
  ᴿ⌊ cs ts ⌋     = CS ᴿ⌊ ts ⌋
  ᴿ⌊ nec ps ts ⌋ = NEC ᴿ⌊ ps ⌋ ᴿ⌊ ts ⌋
  ᴿ⌊ cdist ts ⌋  = CDIST ᴿ⌊ ts ⌋
  ᴿ⌊ cup ts ⌋    = CUP ᴿ⌊ ts ⌋
  ᴿ⌊ cdown ts ⌋  = CDOWN ᴿ⌊ ts ⌋
  ᴿ⌊ cpair ts ⌋  = CPAIR ᴿ⌊ ts ⌋
  ᴿ⌊ cfst ts ⌋   = CFST ᴿ⌊ ts ⌋
  ᴿ⌊ csnd ts ⌋   = CSND ᴿ⌊ ts ⌋
  ᴿ⌊ tt ts ⌋     = TT ᴿ⌊ ts ⌋

  REP : ∀ {Ξ A} → ⊦⊢ Ξ , A → Rep
  REP {Ξ} ts = ᴺ⌊ Ξ ⌋ , ᴿ⌊ ts ⌋

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊦⊢ Ξ , A)

rep : ∀ {A} → ⊢ A → Rep
rep (Ξ , ts) = REP ts


-- Concatenation of derivations.

_⧺⊦_ : ∀ {Ξ Ξ′} → ⊦⊢ Ξ → ⊦⊢ Ξ′ → ⊦⊢ Ξ ⧺ Ξ′
us ⧺⊦ nil       = us
us ⧺⊦ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧺⊦ ts)
us ⧺⊦ ci ts     = ci (us ⧺⊦ ts)
us ⧺⊦ ck ts     = ck (us ⧺⊦ ts)
us ⧺⊦ cs ts     = cs (us ⧺⊦ ts)
us ⧺⊦ nec ps ts = nec ps (us ⧺⊦ ts)
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

box : ∀ {A} → (p : ⊢ A) → ⊢ [ rep p ] A
box (Ξ , ps) = ⌀ , nec ps nil
