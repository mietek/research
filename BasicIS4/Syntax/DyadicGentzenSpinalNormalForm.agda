-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.
-- Normal forms, neutrals, and spines.

module BasicIS4.Syntax.DyadicGentzenSpinalNormalForm where

open import BasicIS4.Syntax.DyadicGentzen public


-- Commuting propositions for neutrals.

data Tyⁿᵉ : Ty → Set where
  α_ : (P : Atom) → Tyⁿᵉ (α P)
  □_ : (A : Ty) → Tyⁿᵉ (□ A)


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx² Ty Ty → Ty → Set where
    neⁿᶠ   : ∀ {A Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B Γ Δ} → Γ , A ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ▻ B
    boxⁿᶠ  : ∀ {A Γ Δ}   → ∅ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ □ A
    pairⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ : ∀ {Γ Δ}     → Γ ⁏ Δ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx² Ty Ty → Ty → Set where
    spⁿᵉ : ∀ {A B C Γ Δ} → A ∈ Γ → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ⊢ⁿᵉ C

--    varⁿᵉ   : ∀ {A Γ Δ}   → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᵉ A
--    appⁿᵉ   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᵉ B
--    mvarⁿᵉ  : ∀ {A Γ Δ}   → A ∈ Δ → Γ ⁏ Δ ⊢ⁿᵉ A
--    unboxⁿᵉ : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ □ A → Γ ⁏ Δ , A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᵉ C
--    fstⁿᵉ   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ A
--    sndⁿᵉ   : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ B

  -- Spines.
  infix 3 _⊢ˢᵖ_⦙_
  data _⊢ˢᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilˢᵖ : ∀ {C} → Γ ⊢ˢᵖ C ⦙ C
    appˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⁏ {!!} ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ▻ B ⦙ C
    fstˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C
    sndˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C

  -- Spine tips.
  infix 3 _⊢ᵗᵖ_⦙_
  data _⊢ᵗᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilᵗᵖ  : ∀ {C} → Γ ⊢ᵗᵖ C ⦙ C
--    boomᵗᵖ : ∀ {C}     → Γ ⊢ᵗᵖ ⊥ ⦙ C
--    caseᵗᵖ : ∀ {A B C} → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ᵗᵖ A ∨ B ⦙ C
