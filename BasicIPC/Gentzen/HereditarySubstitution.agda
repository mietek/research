module BasicIPC.Gentzen.HereditarySubstitution where

open import BasicIPC.Gentzen public


-- Derivations, as Gentzen-style natural deduction trees, following Keller and Altenkirch.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {P}   → Γ ⊢ⁿᵉ α P → Γ ⊢ⁿᶠ α P
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    ttⁿᶠ   : Γ ⊢ⁿᶠ ⊤

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


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm ttⁿᶠ         = tt

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
  mono⊢ⁿᶠ η ttⁿᶠ         = ttⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ i xs) = spⁿᵉ (mono∈ η i) (mono⊢ˢᵖ η xs)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ A ⦙ C → Γ′ ⊢ˢᵖ A ⦙ C
  mono⊢ˢᵖ η nilˢᵖ        = nilˢᵖ
  mono⊢ˢᵖ η (appˢᵖ xs u) = appˢᵖ (mono⊢ˢᵖ η xs) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ xs)   = fstˢᵖ (mono⊢ˢᵖ η xs)
  mono⊢ˢᵖ η (sndˢᵖ xs)   = sndˢᵖ (mono⊢ˢᵖ η xs)


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ - i ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs) | same   = reduce s ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs) | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t           = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u        = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ ttⁿᶠ              = ttⁿᶠ

  [_≔_]ˢᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ˢᵖ B ⦙ C → Γ - i ⊢ˢᵖ B ⦙ C
  [ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ ([ i ≔ s ]ˢᵖ xs)

  reduce : ∀ {A C Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ⁿᶠ C
  reduce t            nilˢᵖ        = t
  reduce (lamⁿᶠ t)    (appˢᵖ xs u) = reduce ([ top ≔ u ]ⁿᶠ t) xs
  reduce (pairⁿᶠ t u) (fstˢᵖ xs)   = reduce t xs
  reduce (pairⁿᶠ t u) (sndˢᵖ xs)   = reduce u xs


-- Reduction-based normal forms.

appⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B
appⁿᶠ t u = reduce t (appˢᵖ nilˢᵖ u)

fstⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ A
fstⁿᶠ t = reduce t (fstˢᵖ nilˢᵖ)

sndⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ B
sndⁿᶠ t = reduce t (sndˢᵖ nilˢᵖ)


-- Useful equipment for deriving neutrals.

≪appˢᵖ : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ C ⦙ B
≪appˢᵖ nilˢᵖ        t = appˢᵖ nilˢᵖ t
≪appˢᵖ (appˢᵖ xs u) t = appˢᵖ (≪appˢᵖ xs t) u
≪appˢᵖ (fstˢᵖ xs)   t = fstˢᵖ (≪appˢᵖ xs t)
≪appˢᵖ (sndˢᵖ xs)   t = sndˢᵖ (≪appˢᵖ xs t)

≪fstˢᵖ : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⊢ˢᵖ C ⦙ A
≪fstˢᵖ nilˢᵖ        = fstˢᵖ nilˢᵖ
≪fstˢᵖ (appˢᵖ xs u) = appˢᵖ (≪fstˢᵖ xs) u
≪fstˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪fstˢᵖ xs)
≪fstˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪fstˢᵖ xs)

≪sndˢᵖ : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⊢ˢᵖ C ⦙ B
≪sndˢᵖ nilˢᵖ        = sndˢᵖ nilˢᵖ
≪sndˢᵖ (appˢᵖ xs u) = appˢᵖ (≪sndˢᵖ xs) u
≪sndˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪sndˢᵖ xs)
≪sndˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪sndˢᵖ xs)


-- Derived neutrals.

varⁿᵉ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᵉ A
varⁿᵉ i = spⁿᵉ i nilˢᵖ

appⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ i xs) t = spⁿᵉ i (≪appˢᵖ xs t)

fstⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ i xs) = spⁿᵉ i (≪fstˢᵖ xs)

sndⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ i xs) = spⁿᵉ i (≪sndˢᵖ xs)


-- Iterated expansion.

expand : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
expand {α P}   t = neⁿᶠ t
expand {A ▻ B} t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {A ∧ B} t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))
expand {⊤}    t = ttⁿᶠ


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)


-- Translation from terms to normal forms.

tm→nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
tm→nf (var i)    = varⁿᶠ i
tm→nf (lam t)    = lamⁿᶠ (tm→nf t)
tm→nf (app t u)  = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (pair t u) = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)    = fstⁿᶠ (tm→nf t)
tm→nf (snd t)    = sndⁿᶠ (tm→nf t)
tm→nf tt         = ttⁿᶠ


-- Normalisation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = nf→tm ∘ tm→nf
