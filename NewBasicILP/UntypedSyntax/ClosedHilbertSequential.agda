-- Hilbert-style formalisation of closed syntax.
-- Sequences of terms.

module NewBasicILP.UntypedSyntax.ClosedHilbertSequential where

open import NewBasicILP.UntypedSyntax.Common public


-- Closed, untyped representations.

data Rep : ℕ → Set where
  NIL   : Rep zero
  MP    : ∀ {n} → Fin n → Fin n → Rep n → Rep (suc n)
  CI    : ∀ {n} → Rep n → Rep (suc n)
  CK    : ∀ {n} → Rep n → Rep (suc n)
  CS    : ∀ {n} → Rep n → Rep (suc n)
  NEC   : ∀ {n} → ∀ {`n} → Rep (suc `n) → Rep n → Rep (suc n)
  CDIST : ∀ {n} → Rep n → Rep (suc n)
  CUP   : ∀ {n} → Rep n → Rep (suc n)
  CDOWN : ∀ {n} → Rep n → Rep (suc n)
  CPAIR : ∀ {n} → Rep n → Rep (suc n)
  CFST  : ∀ {n} → Rep n → Rep (suc n)
  CSND  : ∀ {n} → Rep n → Rep (suc n)
  TT    : ∀ {n} → Rep n → Rep (suc n)


-- Anti-bug wrappers.

record Proof : Set where
  constructor [_]
  field
    {len} : ℕ
    rep   : Rep (suc len)

open ClosedSyntax (Proof) public


-- Concatenation of representations.

_⧺ᴿ_ : ∀ {n₁ n₂} → Rep n₁ → Rep n₂ → Rep (n₁ + n₂)
r₁ ⧺ᴿ NIL       = r₁
r₁ ⧺ᴿ MP i j r₂ = MP (monoFin weak≤+₂ i) (monoFin weak≤+₂ j) (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CI r₂     = CI (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CK r₂     = CK (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CS r₂     = CS (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ NEC `r r₂ = NEC `r (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CDIST r₂  = CDIST (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CUP r₂    = CUP (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CDOWN r₂  = CDOWN (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CPAIR r₂  = CPAIR (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CFST r₂   = CFST (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ CSND r₂   = CSND (r₁ ⧺ᴿ r₂)
r₁ ⧺ᴿ TT r₂     = TT (r₁ ⧺ᴿ r₂)


-- Modus ponens and necessitation in nested form.

APP : ∀ {n₁ n₂} → Rep (suc n₁) → Rep (suc n₂) → Rep (suc (suc n₂ + suc n₁))
APP {n₁} {n₂} r₁ r₂ = MP zero (monoFin (weak≤+₁ (suc n₁)) zero) (r₂ ⧺ᴿ r₁)

BOX : ∀ {n} → Rep (suc n) → Rep (suc zero)
BOX {n} r = NEC r NIL


-- Derivations.

mutual
  infix 3 ⊢ᴰ_
  data ⊢ᴰ_ : Cx Ty → Set where
    nil   : ⊢ᴰ ∅
    mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊢ᴰ Ξ → ⊢ᴰ Ξ , B
    ci    : ∀ {Ξ A}     → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ A
    ck    : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ B ▻ A
    cs    : ∀ {Ξ A B C} → ⊢ᴰ Ξ → ⊢ᴰ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    nec   : ∀ {Ξ A}     → ∀ {`Ξ} → (d : ⊢ᴰ `Ξ , A)
                        → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ ᴿ⌊ d ⌋ ] ⦂ A

    cdist : ∀ {Ξ A B}   → ∀ {n₁ n₂} → {r₁ : Rep (suc n₁)} → {r₂ : Rep (suc n₂)}
                        → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ r₁ ] ⦂ (A ▻ B) ▻ [ r₂ ] ⦂ A ▻ [ APP r₁ r₂ ] ⦂ B

    cup   : ∀ {Ξ A}     → ∀ {n} → {r : Rep (suc n)}
                        → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ r ] ⦂ A ▻ [ BOX r ] ⦂ [ r ] ⦂ A

    cdown : ∀ {Ξ A}     → ∀ {n} → {r : Rep (suc n)}
                        → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ r ] ⦂ A ▻ A

    cpair : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ B ▻ A ∧ B
    cfst  : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ∧ B ▻ A
    csnd  : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ∧ B ▻ B
    tt    : ∀ {Ξ}       → ⊢ᴰ Ξ → ⊢ᴰ Ξ , ⊤


  -- Projection from derivations to representations.

  ᴿ⌊_⌋ : ∀ {Ξ} → ⊢ᴰ Ξ → Rep ᴺ⌊ Ξ ⌋
  ᴿ⌊ nil ⌋      = NIL
  ᴿ⌊ mp i j d ⌋ = MP ⁱ⌊ i ⌋ ⁱ⌊ j ⌋ ᴿ⌊ d ⌋
  ᴿ⌊ ci d ⌋     = CI ᴿ⌊ d ⌋
  ᴿ⌊ ck d ⌋     = CK ᴿ⌊ d ⌋
  ᴿ⌊ cs d ⌋     = CS ᴿ⌊ d ⌋
  ᴿ⌊ nec `d d ⌋ = NEC ᴿ⌊ `d ⌋ ᴿ⌊ d ⌋
  ᴿ⌊ cdist d ⌋  = CDIST ᴿ⌊ d ⌋
  ᴿ⌊ cup d ⌋    = CUP ᴿ⌊ d ⌋
  ᴿ⌊ cdown d ⌋  = CDOWN ᴿ⌊ d ⌋
  ᴿ⌊ cpair d ⌋  = CPAIR ᴿ⌊ d ⌋
  ᴿ⌊ cfst d ⌋   = CFST ᴿ⌊ d ⌋
  ᴿ⌊ csnd d ⌋   = CSND ᴿ⌊ d ⌋
  ᴿ⌊ tt d ⌋     = TT ᴿ⌊ d ⌋


-- Anti-bug wrappers.

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊢ᴰ Ξ , A)


-- Concatenation of derivations.

_⧺ᴰ_ : ∀ {Ξ₁ Ξ₂} → ⊢ᴰ Ξ₁ → ⊢ᴰ Ξ₂ → ⊢ᴰ Ξ₁ ⧺ Ξ₂
d₁ ⧺ᴰ nil       = d₁
d₁ ⧺ᴰ mp i j d₂ = mp (mono∈ weak⊆⧺₂ i) (mono∈ weak⊆⧺₂ j) (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ ci d₂     = ci (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ ck d₂     = ck (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cs d₂     = cs (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ nec `d d₂ = nec `d (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cdist d₂  = cdist (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cup d₂    = cup (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cdown d₂  = cdown (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cpair d₂  = cpair (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ cfst d₂   = cfst (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ csnd d₂   = csnd (d₁ ⧺ᴰ d₂)
d₁ ⧺ᴰ tt d₂     = tt (d₁ ⧺ᴰ d₂)


-- Modus ponens and necessitation in nested form.

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Ξ₁ , d₁) (Ξ₂ , d₂) = Ξ₃ , d₃
  where Ξ₃ = (Ξ₂ , A) ⧺ (Ξ₁ , A ▻ B)
        d₃ = mp top (mono∈ (weak⊆⧺₁ (Ξ₁ , A ▻ B)) top) (d₂ ⧺ᴰ d₁)

box : ∀ {A} → (t : ⊢ A) → ⊢ [ ᴿ⌊ π₂ t ⌋ ] ⦂ A
box (Ξ , d) = ∅ , nec d nil
