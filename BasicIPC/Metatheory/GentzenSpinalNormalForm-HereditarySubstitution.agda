module BasicIPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution where

open import BasicIPC.Syntax.GentzenSpinalNormalForm public


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ ∖ i ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ∖ i ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs) | same   = reduce s ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs) | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t           = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u        = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ            = unitⁿᶠ

  [_≔_]ˢᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ ∖ i ⊢ⁿᶠ A → Γ ⊢ˢᵖ B ⦙ C → Γ ∖ i ⊢ˢᵖ B ⦙ C
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
expand {⊤}    t = unitⁿᶠ


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)


-- Translation from simple terms to normal forms.

tm→nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
tm→nf (var i)    = varⁿᶠ i
tm→nf (lam t)    = lamⁿᶠ (tm→nf t)
tm→nf (app t u)  = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (pair t u) = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)    = fstⁿᶠ (tm→nf t)
tm→nf (snd t)    = sndⁿᶠ (tm→nf t)
tm→nf unit       = unitⁿᶠ


-- Normalisation by hereditary substitution.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = nf→tm ∘ tm→nf
