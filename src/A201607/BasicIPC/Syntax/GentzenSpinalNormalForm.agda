{-# OPTIONS --sized-types #-}

-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Gentzen-style formalisation of syntax.
-- Normal forms, neutrals, and spines.

module A201607.BasicIPC.Syntax.GentzenSpinalNormalForm where

open import A201607.BasicIPC.Syntax.Gentzen public


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {P}   → Γ ⊢ⁿᵉ α P → Γ ⊢ⁿᶠ α P
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    spⁿᵉ : ∀ {A C} → A ∈ Γ → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ⁿᵉ C

  -- Spines.
  infix 3 _⊢ˢᵖ_⦙_
  data _⊢ˢᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilˢᵖ : ∀ {C}     → Γ ⊢ˢᵖ C ⦙ C
    appˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ▻ B ⦙ C
    fstˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C
    sndˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C


-- Translation from normal forms to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (spⁿᵉ i xs) = sp→tm (var i) xs

  sp→tm : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ C
  sp→tm t nilˢᵖ        = t
  sp→tm t (appˢᵖ xs u) = sp→tm (app t (nf→tm u)) xs
  sp→tm t (fstˢᵖ xs)   = sp→tm (fst t) xs
  sp→tm t (sndˢᵖ xs)   = sp→tm (snd t) xs


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ i xs) = spⁿᵉ (mono∈ η i) (mono⊢ˢᵖ η xs)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ A ⦙ C → Γ′ ⊢ˢᵖ A ⦙ C
  mono⊢ˢᵖ η nilˢᵖ        = nilˢᵖ
  mono⊢ˢᵖ η (appˢᵖ xs u) = appˢᵖ (mono⊢ˢᵖ η xs) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ xs)   = fstˢᵖ (mono⊢ˢᵖ η xs)
  mono⊢ˢᵖ η (sndˢᵖ xs)   = sndˢᵖ (mono⊢ˢᵖ η xs)
