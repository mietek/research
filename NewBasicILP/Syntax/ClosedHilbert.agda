module NewBasicILP.Syntax.ClosedHilbert where

open import NewBasicILP.Syntax.Common public


-- Types and derivations.

mutual
  infixr 9 [_]_
  infixl 8 _∧_
  infixr 6 _▻_
  data Ty : Set where
    α_   : Atom → Ty
    _▻_  : Ty → Ty → Ty
    [_]_ : ∀ {A} → ⊢ A → Ty → Ty
    _∧_  : Ty → Ty → Ty
    ⊤   : Ty

  infix 3 ⊢_
  data ⊢_ : Ty → Set where
    app   : ∀ {A B}   → ⊢ A ▻ B → ⊢ A → ⊢ B
    ci    : ∀ {A}     → ⊢ A ▻ A
    ck    : ∀ {A B}   → ⊢ A ▻ B ▻ A
    cs    : ∀ {A B C} → ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C

    box   : ∀ {A}     → (p : ⊢ A)
                      → ⊢ [ p ] A

    cdist : ∀ {A B}   → {p : ⊢ A ▻ B} → {q : ⊢ A}
                      → ⊢ [ p ] (A ▻ B) ▻ [ q ] A ▻ [ app p q ] B

    cup   : ∀ {A}     → {p : ⊢ A}
                      → ⊢ [ p ] A ▻ [ box p ] [ p ] A

    cdown : ∀ {A}     → {p : ⊢ A}
                      → ⊢ [ p ] A ▻ A

    cpair : ∀ {A B}   → ⊢ A ▻ B ▻ A ∧ B
    cfst  : ∀ {A B}   → ⊢ A ∧ B ▻ A
    csnd  : ∀ {A B}   → ⊢ A ∧ B ▻ B
    tt    : ⊢ ⊤
