-- Hilbert-style formalisation of closed syntax.
-- Nested terms.

module OldBasicILP.UntypedSyntax.ClosedHilbert where

open import OldBasicILP.UntypedSyntax.Common public


-- Closed, untyped representations.

data Rep : Set where
  APP   : Rep → Rep → Rep
  CI    : Rep
  CK    : Rep
  CS    : Rep
  BOX   : Rep → Rep
  CDIST : Rep
  CUP   : Rep
  CDOWN : Rep
  CPAIR : Rep
  CFST  : Rep
  CSND  : Rep
  UNIT  : Rep


-- Anti-bug wrappers.

record Proof : Set where
  constructor [_]
  field
    rep : Rep

open ClosedSyntax (Proof) public


-- Derivations using representations in types.

mutual
  infix 3 ⊢_
  data ⊢_ : Ty → Set where
    app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
    ci    : ∀ {A}     → ⊢ A ▻ A
    ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
    cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    box   : ∀ {A}     → (d : ⊢ A)
                      → ⊢ [ ᴿ⌊ d ⌋ ] ⦂ A

    cdist : ∀ {A B}   → {r₁ r₂ : Rep}
                      → ⊢ [ r₁ ] ⦂ (A ▻ B) ▻ [ r₂ ] ⦂ A ▻ [ APP r₁ r₂ ] ⦂ B

    cup   : ∀ {A}     → {r : Rep}
                      → ⊢ [ r ] ⦂ A ▻ [ BOX r ] ⦂ [ r ] ⦂ A

    cdown : ∀ {A}     → {r : Rep}
                      → ⊢ [ r ] ⦂ A ▻ A

    cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
    cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
    csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
    unit  : ⊢ ⊤


  -- Projection from derivations to representations.

  ᴿ⌊_⌋ : ∀ {A} → ⊢ A → Rep
  ᴿ⌊ app d₁ d₂ ⌋ = APP ᴿ⌊ d₁ ⌋ ᴿ⌊ d₂ ⌋
  ᴿ⌊ ci ⌋        = CI
  ᴿ⌊ ck ⌋        = CK
  ᴿ⌊ cs ⌋        = CS
  ᴿ⌊ box d ⌋     = BOX ᴿ⌊ d ⌋
  ᴿ⌊ cdist ⌋     = CDIST
  ᴿ⌊ cup ⌋       = CUP
  ᴿ⌊ cdown ⌋     = CDOWN
  ᴿ⌊ cpair ⌋     = CPAIR
  ᴿ⌊ cfst ⌋      = CFST
  ᴿ⌊ csnd ⌋      = CSND
  ᴿ⌊ unit ⌋      = UNIT

infix 3 ⊢⋆_
⊢⋆_ : Cx Ty → Set
⊢⋆ ∅     = 𝟙
⊢⋆ Ξ , A = ⊢⋆ Ξ × ⊢ A


-- Cut and multicut.

cut : ∀ {A B} → ⊢ A → ⊢ A ▻ B → ⊢ B
cut d₁ d₂ = app d₂ d₁

multicut : ∀ {Ξ A} → ⊢⋆ Ξ → ⊢ Ξ ▻⋯▻ A → ⊢ A
multicut {∅}     ∙         d₂ = d₂
multicut {Ξ , B} (ds , d₁) d₂ = app (multicut ds d₂) d₁


-- Contraction.

ccont : ∀ {A B} → ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = app (app cs cs) (app ck ci)

cont : ∀ {A B} → ⊢ A ▻ A ▻ B → ⊢ A ▻ B
cont d = app ccont d


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = app (app cs (app (app cs (app ck cs))
                         (app (app cs (app ck ck)) cs)))
            (app ck ck)

exch : ∀ {A B C} → ⊢ A ▻ B ▻ C → ⊢ B ▻ A ▻ C
exch d = app cexch d


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C} → ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = app (app cs (app ck cs)) ck

comp : ∀ {A B C} → ⊢ B ▻ C → ⊢ A ▻ B → ⊢ A ▻ C
comp d₁ d₂ = app (app ccomp d₁) d₂


-- Useful theorems in functional form.

dist : ∀ {A B r₁ r₂} → ⊢ [ r₁ ] ⦂ (A ▻ B) → ⊢ [ r₂ ] ⦂ A → ⊢ [ APP r₁ r₂ ] ⦂ B
dist d₁ d₂ = app (app cdist d₁) d₂

up : ∀ {A r} → ⊢ [ r ] ⦂ A → ⊢ [ BOX r ] ⦂ [ r ] ⦂ A
up d = app cup d

down : ∀ {A r} → ⊢ [ r ] ⦂ A → ⊢ A
down d = app cdown d

distup : ∀ {A B r₀ r₁} → ⊢ [ r₁ ] ⦂ ([ r₀ ] ⦂ A ▻ B) → ⊢ [ r₀ ] ⦂ A → ⊢ [ APP r₁ (BOX r₀) ] ⦂ B
distup d₁ d₂ = dist d₁ (up d₂)

pair : ∀ {A B} → ⊢ A → ⊢ B → ⊢ A ∧ B
pair d₁ d₂ = app (app cpair d₁) d₂

fst : ∀ {A B} → ⊢ A ∧ B → ⊢ A
fst d = app cfst d

snd : ∀ {A B} → ⊢ A ∧ B → ⊢ B
snd d = app csnd d
