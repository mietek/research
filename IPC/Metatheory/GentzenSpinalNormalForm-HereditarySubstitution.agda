module A201607.IPC.Metatheory.GentzenSpinalNormalForm-HereditarySubstitution where

open import A201607.IPC.Syntax.GentzenSpinalNormalForm public


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ ∖ i ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ∖ i ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs y) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs y) | same   = reduce s ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs y) | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t             = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u          = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ              = unitⁿᶠ
  [ i ≔ s ]ⁿᶠ inlⁿᶠ t             = inlⁿᶠ ([ i ≔ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ inrⁿᶠ t             = inrⁿᶠ ([ i ≔ s ]ⁿᶠ t)

  [_≔_]ˢᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ ∖ i ⊢ⁿᶠ A → Γ ⊢ˢᵖ B ⦙ C → Γ ∖ i ⊢ˢᵖ B ⦙ C
  [ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ ([ i ≔ s ]ˢᵖ xs)

  [_≔_]ᵗᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ ∖ i ⊢ⁿᶠ A → Γ ⊢ᵗᵖ B ⦙ C → Γ ∖ i ⊢ᵗᵖ B ⦙ C
  [ i ≔ s ]ᵗᵖ nilᵗᵖ      = nilᵗᵖ
  [ i ≔ s ]ᵗᵖ boomᵗᵖ     = boomᵗᵖ
  [ i ≔ s ]ᵗᵖ caseᵗᵖ u v = caseᵗᵖ u′ v′
    where u′ = [ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u
          v′ = [ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ v

  reduce : ∀ {A B C Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ᵗᵖ B ⦙ C → {{_ : Tyⁿᵉ C}} → Γ ⊢ⁿᶠ C
  reduce t                               nilˢᵖ        nilᵗᵖ        = t
  reduce (neⁿᶠ (spⁿᵉ i xs nilᵗᵖ))        nilˢᵖ        y            = neⁿᶠ (spⁿᵉ i xs y)
  reduce (neⁿᶠ (spⁿᵉ i xs boomᵗᵖ))       nilˢᵖ        y            = neⁿᶠ (spⁿᵉ i xs boomᵗᵖ)
  reduce (neⁿᶠ (spⁿᵉ i xs (caseᵗᵖ u v))) nilˢᵖ        y            = neⁿᶠ (spⁿᵉ i xs (caseᵗᵖ u′ v′))
    where u′ = reduce u nilˢᵖ (mono⊢ᵗᵖ weak⊆ y)
          v′ = reduce v nilˢᵖ (mono⊢ᵗᵖ weak⊆ y)
  reduce (neⁿᶠ t {{()}})                 (appˢᵖ xs u) y
  reduce (neⁿᶠ t {{()}})                 (fstˢᵖ xs)   y
  reduce (neⁿᶠ t {{()}})                 (sndˢᵖ xs)   y
  reduce (lamⁿᶠ t)                       (appˢᵖ xs u) y            = reduce ([ top ≔ u ]ⁿᶠ t) xs y
  reduce (pairⁿᶠ t u)                    (fstˢᵖ xs)   y            = reduce t xs y
  reduce (pairⁿᶠ t u)                    (sndˢᵖ xs)   y            = reduce u xs y
  reduce (inlⁿᶠ t)                       nilˢᵖ        (caseᵗᵖ u v) = [ top ≔ t ]ⁿᶠ u
  reduce (inrⁿᶠ t)                       nilˢᵖ        (caseᵗᵖ u v) = [ top ≔ t ]ⁿᶠ v


-- Reduction-based normal forms.

appⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B
appⁿᶠ (neⁿᶠ t {{()}})
appⁿᶠ (lamⁿᶠ t) u = [ top ≔ u ]ⁿᶠ t

fstⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ A
fstⁿᶠ (neⁿᶠ t {{()}})
fstⁿᶠ (pairⁿᶠ t u) = t

sndⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ B
sndⁿᶠ (neⁿᶠ t {{()}})
sndⁿᶠ (pairⁿᶠ t u) = u


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
varⁿᵉ i = spⁿᵉ i nilˢᵖ nilᵗᵖ

appⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        t = spⁿᵉ i (≪appˢᵖ xs t) nilᵗᵖ
appⁿᵉ (spⁿᵉ i xs boomᵗᵖ)       t = spⁿᵉ i xs boomᵗᵖ
appⁿᵉ (spⁿᵉ i xs (caseᵗᵖ u v)) t = spⁿᵉ i xs (caseᵗᵖ u′ v′)
  where u′ = appⁿᶠ u (mono⊢ⁿᶠ weak⊆ t)
        v′ = appⁿᶠ v (mono⊢ⁿᶠ weak⊆ t)

fstⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪fstˢᵖ xs) nilᵗᵖ
fstⁿᵉ (spⁿᵉ i xs boomᵗᵖ)       = spⁿᵉ i xs boomᵗᵖ
fstⁿᵉ (spⁿᵉ i xs (caseᵗᵖ u v)) = spⁿᵉ i xs (caseᵗᵖ (fstⁿᶠ u) (fstⁿᶠ v))

sndⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪sndˢᵖ xs) nilᵗᵖ
sndⁿᵉ (spⁿᵉ i xs boomᵗᵖ)       = spⁿᵉ i xs boomᵗᵖ
sndⁿᵉ (spⁿᵉ i xs (caseᵗᵖ u v)) = spⁿᵉ i xs (caseᵗᵖ (sndⁿᶠ u) (sndⁿᶠ v))


-- Iterated expansion.

expand : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
expand {α P}   t = neⁿᶠ t {{α P}}
expand {A ▻ B} t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {A ∧ B} t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))
expand {⊤}    t = unitⁿᶠ
expand {⊥}    t = neⁿᶠ t {{⊥}}
expand {A ∨ B} t = neⁿᶠ t {{A ∨ B}}


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)

mutual
  boomⁿᶠ : ∀ {C Γ} → Γ ⊢ⁿᶠ ⊥ → Γ ⊢ⁿᶠ C
  boomⁿᶠ (neⁿᶠ t) = expand (boomⁿᵉ t)

  boomⁿᵉ : ∀ {C Γ} → Γ ⊢ⁿᵉ ⊥ → Γ ⊢ⁿᵉ C
  boomⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i xs boomᵗᵖ
  boomⁿᵉ (spⁿᵉ i xs boomᵗᵖ)       = spⁿᵉ i xs boomᵗᵖ
  boomⁿᵉ (spⁿᵉ i xs (caseᵗᵖ u v)) = spⁿᵉ i xs (caseᵗᵖ (boomⁿᶠ u) (boomⁿᶠ v))

mutual
  caseⁿᶠ : ∀ {A B C Γ} → Γ ⊢ⁿᶠ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᶠ C
  caseⁿᶠ (neⁿᶠ t)  u v = expand (caseⁿᵉ t u v)
  caseⁿᶠ (inlⁿᶠ t) u v = [ top ≔ t ]ⁿᶠ u
  caseⁿᶠ (inrⁿᶠ t) u v = [ top ≔ t ]ⁿᶠ v

  caseⁿᵉ : ∀ {A B C Γ} → Γ ⊢ⁿᵉ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C
  caseⁿᵉ (spⁿᵉ i xs nilᵗᵖ)          u v = spⁿᵉ i xs (caseᵗᵖ u v)
  caseⁿᵉ (spⁿᵉ i xs boomᵗᵖ)         u v = spⁿᵉ i xs boomᵗᵖ
  caseⁿᵉ (spⁿᵉ i xs (caseᵗᵖ tᵤ tᵥ)) u v = spⁿᵉ i xs (caseᵗᵖ u′ v′)
    where u′ = caseⁿᶠ tᵤ (mono⊢ⁿᶠ (keep weak⊆) u) (mono⊢ⁿᶠ (keep weak⊆) v)
          v′ = caseⁿᶠ tᵥ (mono⊢ⁿᶠ (keep weak⊆) u) (mono⊢ⁿᶠ (keep weak⊆) v)


-- Translation from terms to normal forms.

tm→nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
tm→nf (var i)      = varⁿᶠ i
tm→nf (lam t)      = lamⁿᶠ (tm→nf t)
tm→nf (app t u)    = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (pair t u)   = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)      = fstⁿᶠ (tm→nf t)
tm→nf (snd t)      = sndⁿᶠ (tm→nf t)
tm→nf unit         = unitⁿᶠ
tm→nf (boom t)     = boomⁿᶠ (tm→nf t)
tm→nf (inl t)      = inlⁿᶠ (tm→nf t)
tm→nf (inr t)      = inrⁿᶠ (tm→nf t)
tm→nf (case t u v) = caseⁿᶠ (tm→nf t) (tm→nf u) (tm→nf v)


-- Normalisation by hereditary substitution.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = nf→tm ∘ tm→nf
