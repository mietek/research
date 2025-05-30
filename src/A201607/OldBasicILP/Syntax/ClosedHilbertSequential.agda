{-# OPTIONS --sized-types #-}

-- Hilbert-style formalisation of closed syntax.
-- Sequences of terms.

module A201607.OldBasicILP.Syntax.ClosedHilbertSequential where

open import A201607.OldBasicILP.Syntax.Common public


-- Mutually-recursive declarations.

data Ty : Set

record Proof (Ξ : Cx Ty) (A : Ty) : Set

data ⊢ᴰ_ : Cx Ty → Set

_⧺ᴰ_ : ∀ {Ξ₁ Ξ₂} → ⊢ᴰ Ξ₁ → ⊢ᴰ Ξ₂ → ⊢ᴰ Ξ₁ ⧺ Ξ₂


-- Types parametrised by closed derivations.

infixr 10 _⦂_
infixl 9 _∧_
infixr 7 _▻_
data Ty where
  α_  : Atom → Ty
  _▻_ : Ty → Ty → Ty
  _⦂_ : ∀ {Ξ A} → Proof Ξ A → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty


-- Anti-bug wrappers.

record Proof Ξ A where
  inductive
  constructor [_]
  field
    der : ⊢ᴰ Ξ , A


-- More mutually-recursive declarations.

appᴰ : ∀ {Ξ₁ Ξ₂ A B} → ⊢ᴰ Ξ₁ , A ▻ B → ⊢ᴰ Ξ₂ , A → ⊢ᴰ (Ξ₂ , A) ⧺ (Ξ₁ , A ▻ B) , B

boxᴰ : ∀ {Ξ A} → (d : ⊢ᴰ Ξ , A) → ⊢ᴰ ∅ , [ d ] ⦂ A


-- Derivations.

infix 3 ⊢ᴰ_
data ⊢ᴰ_ where
  nil   : ⊢ᴰ ∅
  mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊢ᴰ Ξ → ⊢ᴰ Ξ , B
  ci    : ∀ {Ξ A}     → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ A
  ck    : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C} → ⊢ᴰ Ξ → ⊢ᴰ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

  nec   : ∀ {Ξ A}     → ∀ {`Ξ} → (`d : ⊢ᴰ `Ξ , A)
                      → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ `d ] ⦂ A

  cdist : ∀ {Ξ A B}   → ∀ {`Ξ₁ `Ξ₂} → {`d₁ : ⊢ᴰ `Ξ₁ , A ▻ B} → {`d₂ : ⊢ᴰ `Ξ₂ , A}
                      → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ `d₁ ] ⦂ (A ▻ B) ▻ [ `d₂ ] ⦂ A ▻ [ appᴰ `d₁ `d₂ ] ⦂ B

  cup   : ∀ {Ξ A}     → ∀ {`Ξ} → {`d : ⊢ᴰ `Ξ , A}
                      → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ `d ] ⦂ A ▻ [ boxᴰ `d ] ⦂ [ `d ] ⦂ A

  cdown : ∀ {Ξ A}     → ∀ {`Ξ} → {`d : ⊢ᴰ `Ξ , A}
                      → ⊢ᴰ Ξ → ⊢ᴰ Ξ , [ `d ] ⦂ A ▻ A

  cpair : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B}   → ⊢ᴰ Ξ → ⊢ᴰ Ξ , A ∧ B ▻ B
  unit  : ∀ {Ξ}       → ⊢ᴰ Ξ → ⊢ᴰ Ξ , ⊤


-- Anti-bug wrappers.

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊢ᴰ Ξ , A)


-- Concatenation of derivations.

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
d₁ ⧺ᴰ unit d₂   = unit (d₁ ⧺ᴰ d₂)


-- Modus ponens and necessitation in nested form.

appᴰ {Ξ₁} {Ξ₂} {A} {B} d₁ d₂ = mp top (mono∈ (weak⊆⧺₁ (Ξ₁ , A ▻ B)) top) (d₂ ⧺ᴰ d₁)

boxᴰ {Ξ} {A} d = nec d nil

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Ξ₁ , d₁) (Ξ₂ , d₂) = Ξ₃ , d₃
  where Ξ₃ = (Ξ₂ , A) ⧺ (Ξ₁ , A ▻ B)
        d₃ = appᴰ d₁ d₂

box : ∀ {A} → (t : ⊢ A) → ⊢ [ π₂ t ] ⦂ A
box (Ξ , d) = ∅ , boxᴰ d
