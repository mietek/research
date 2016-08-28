module NewBasicILP.Syntax.ClosedHilbertSequential where

open import NewBasicILP.Syntax.Common public


-- Mutual declarations.

data Ty : Set
data ⊦⊢_ : Cx Ty → Set
_⧺⊦_ : ∀ {Ξ Ξ′} → ⊦⊢ Ξ → ⊦⊢ Ξ′ → ⊦⊢ Ξ ⧺ Ξ′


-- Types.

infixr 9 [_]_
infixl 8 _∧_
infixr 6 _▻_
data Ty where
  α_   : Atom → Ty
  _▻_  : Ty → Ty → Ty
  [_]_ : ∀ {Ξ A} → ⊦⊢ Ξ , A → Ty → Ty
  _∧_  : Ty → Ty → Ty
  ⊤   : Ty

APP : ∀ {Ξ′ A Ξ B} → ⊦⊢ Ξ , A ▻ B → ⊦⊢ Ξ′ , A → ⊦⊢ (Ξ , A ▻ B) ⧺ (Ξ′ , A) , B
BOX : ∀ {Ξ A} → (ps : ⊦⊢ Ξ , A) → ⊦⊢ ⌀ , [ ps ] A


-- Derivations.

infix 3 ⊦⊢_
data ⊦⊢_ where
  nil   : ⊦⊢ ⌀
  mp    : ∀ {Ξ A B}   → A ▻ B ∈ Ξ → A ∈ Ξ → ⊦⊢ Ξ → ⊦⊢ Ξ , B
  ci    : ∀ {Ξ A}     → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ A
  ck    : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A
  cs    : ∀ {Ξ A B C} → ⊦⊢ Ξ → ⊦⊢ Ξ , (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

  nec   : ∀ {Ξ A}     → ∀ {Ξ′} → (ps : ⊦⊢ Ξ′ , A)
                      → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] A

  cdist : ∀ {Ξ A B}   → ∀ {Ξ′ Ξ″} → {ps : ⊦⊢ Ξ′ , A ▻ B} → {qs : ⊦⊢ Ξ″ , A}
                      → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] (A ▻ B) ▻ [ qs ] A ▻ [ APP ps qs ] B

  cup   : ∀ {Ξ A}     → ∀ {Ξ′} → {ps : ⊦⊢ Ξ′ , A}
                      → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] A ▻ [ BOX ps ] [ ps ] A

  cdown : ∀ {Ξ A}     → ∀ {Ξ′} → {ps : ⊦⊢ Ξ′ , A}
                      → ⊦⊢ Ξ → ⊦⊢ Ξ , [ ps ] A ▻ A

  cpair : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ▻ B ▻ A ∧ B
  cfst  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ A
  csnd  : ∀ {Ξ A B}   → ⊦⊢ Ξ → ⊦⊢ Ξ , A ∧ B ▻ B
  tt    : ∀ {Ξ}       → ⊦⊢ Ξ → ⊦⊢ Ξ , ⊤

APP {Ξ′} {A} ps qs = mp (mono∈ (weak⊆⧺ₗ (Ξ′ , A)) top) top (ps ⧺⊦ qs)
BOX ps = nec ps nil

infix 3 ⊢_
⊢_ : Ty → Set
⊢ A = ∃ (λ Ξ → ⊦⊢ Ξ , A)

der : ∀ {A} (p : ⊢ A) → ⊦⊢ (π₁ p , A)
der p = π₂ p


-- Concatenation of derivations.

us ⧺⊦ nil       = us
us ⧺⊦ mp i j ts = mp (mono∈ weak⊆⧺ᵣ i) (mono∈ weak⊆⧺ᵣ j) (us ⧺⊦ ts)
us ⧺⊦ ci ts     = ci (us ⧺⊦ ts)
us ⧺⊦ ck ts     = ck (us ⧺⊦ ts)
us ⧺⊦ cs ts     = cs (us ⧺⊦ ts)
us ⧺⊦ nec ss ts = nec ss (us ⧺⊦ ts)
us ⧺⊦ cdist ts  = cdist (us ⧺⊦ ts)
us ⧺⊦ cup ts    = cup (us ⧺⊦ ts)
us ⧺⊦ cdown ts  = cdown (us ⧺⊦ ts)
us ⧺⊦ cpair ts  = cpair (us ⧺⊦ ts)
us ⧺⊦ cfst ts   = cfst (us ⧺⊦ ts)
us ⧺⊦ csnd ts   = csnd (us ⧺⊦ ts)
us ⧺⊦ tt ts     = tt (us ⧺⊦ ts)


-- Modus ponens and necessitation in expanded form.

app : ∀ {A B} → ⊢ A ▻ B → ⊢ A → ⊢ B
app {A} {B} (Ξ , ps) (Ξ′ , qs) = ((Ξ , A ▻ B) ⧺ (Ξ′ , A)) , APP ps qs

box : ∀ {A} → (p : ⊢ A) → ⊢ [ der p ] A
box (Ξ , ps) = ⌀ , BOX ps
