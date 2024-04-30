-- Intuitionistic propositional calculus.
-- Gentzen-style formalisation of syntax.
-- Normal forms, neutrals, and spines.

module A201607.IPC.Syntax.GentzenSpinalNormalForm where

open import A201607.IPC.Syntax.Gentzen public


-- Commuting propositions for neutrals.

data Tyⁿᵉ : Ty → Set where
  α_  : (P : Atom) → Tyⁿᵉ (α P)
  ⊥  : Tyⁿᵉ ⊥
  _∨_ : (A B : Ty) → Tyⁿᵉ (A ∨ B)


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → {{_ : Tyⁿᵉ A}} → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ⊤
    inlⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A ∨ B
    inrⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∨ B

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    spⁿᵉ : ∀ {A B C} → A ∈ Γ → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ᵗᵖ B ⦙ C → Γ ⊢ⁿᵉ C

  -- Spines.
  infix 3 _⊢ˢᵖ_⦙_
  data _⊢ˢᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilˢᵖ : ∀ {C}     → Γ ⊢ˢᵖ C ⦙ C
    appˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ▻ B ⦙ C
    fstˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C
    sndˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C

  -- Spine tips.
  infix 3 _⊢ᵗᵖ_⦙_
  data _⊢ᵗᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilᵗᵖ  : ∀ {C}     → Γ ⊢ᵗᵖ C ⦙ C
    boomᵗᵖ : ∀ {C}     → Γ ⊢ᵗᵖ ⊥ ⦙ C
    caseᵗᵖ : ∀ {A B C} → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ᵗᵖ A ∨ B ⦙ C


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit
  nf→tm (inlⁿᶠ t)    = inl (nf→tm t)
  nf→tm (inrⁿᶠ t)    = inr (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (spⁿᵉ i xs y) = tp→tm (var i) xs y

  sp→tm : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ C
  sp→tm t nilˢᵖ        = t
  sp→tm t (appˢᵖ xs u) = sp→tm (app t (nf→tm u)) xs
  sp→tm t (fstˢᵖ xs)   = sp→tm (fst t) xs
  sp→tm t (sndˢᵖ xs)   = sp→tm (snd t) xs

  tp→tm : ∀ {A B C Γ} → Γ ⊢ A → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ᵗᵖ B ⦙ C → Γ ⊢ C
  tp→tm t xs nilᵗᵖ        = sp→tm t xs
  tp→tm t xs boomᵗᵖ       = boom (sp→tm t xs)
  tp→tm t xs (caseᵗᵖ u v) = case (sp→tm t xs) (nf→tm u) (nf→tm v)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η (inlⁿᶠ t)    = inlⁿᶠ (mono⊢ⁿᶠ η t)
  mono⊢ⁿᶠ η (inrⁿᶠ t)    = inrⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ i xs y) = spⁿᵉ (mono∈ η i) (mono⊢ˢᵖ η xs) (mono⊢ᵗᵖ η y)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ A ⦙ C → Γ′ ⊢ˢᵖ A ⦙ C
  mono⊢ˢᵖ η nilˢᵖ        = nilˢᵖ
  mono⊢ˢᵖ η (appˢᵖ xs u) = appˢᵖ (mono⊢ˢᵖ η xs) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ xs)   = fstˢᵖ (mono⊢ˢᵖ η xs)
  mono⊢ˢᵖ η (sndˢᵖ xs)   = sndˢᵖ (mono⊢ˢᵖ η xs)

  mono⊢ᵗᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ᵗᵖ A ⦙ C → Γ′ ⊢ᵗᵖ A ⦙ C
  mono⊢ᵗᵖ η nilᵗᵖ        = nilᵗᵖ
  mono⊢ᵗᵖ η boomᵗᵖ       = boomᵗᵖ
  mono⊢ᵗᵖ η (caseᵗᵖ u v) = caseᵗᵖ (mono⊢ⁿᶠ (keep η) u) (mono⊢ⁿᶠ (keep η) v)
