{-# OPTIONS --sized-types #-}

module A201607.BasicICML.Metatheory.DyadicGentzenSpinalNormalForm-HereditarySubstitution where

open import A201607.BasicICML.Syntax.DyadicGentzenSpinalNormalForm public


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ∖ i ⁏ Δ ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs y)        with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs y)        | same   = reduce s ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs y)        | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y))
  [ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ j ts xs y)     = neⁿᶠ (mspⁿᵉ j ([ i ≔ s ]⋆ⁿᶠ ts) ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t                    = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ boxⁿᶠ t                    = boxⁿᶠ t
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u                 = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ                     = unitⁿᶠ

  [_≔_]ˢᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ∖ i ⁏ Δ ⊢ˢᵖ B ⦙ C
  [ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ ([ i ≔ s ]ˢᵖ xs)

  [_≔_]ᵗᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ∖ i ⁏ Δ ⊢ᵗᵖ B ⦙ C
  [ i ≔ s ]ᵗᵖ nilᵗᵖ     = nilᵗᵖ
  [ i ≔ s ]ᵗᵖ unboxᵗᵖ u = unboxᵗᵖ u′
    where u′ = [ i ≔ mmono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u

  [_≔_]⋆ⁿᶠ : ∀ {Ξ A Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Γ ∖ i ⁏ Δ ⊢⋆ⁿᶠ Ξ
  [_≔_]⋆ⁿᶠ {∅}     i s ∙        = ∙
  [_≔_]⋆ⁿᶠ {Ξ , B} i s (ts , t) = [ i ≔ s ]⋆ⁿᶠ ts , [ i ≔ s ]ⁿᶠ t

  m[_≔_]ⁿᶠ_ : ∀ {Ψ A B Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ∖ i ⊢ⁿᶠ B
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j xs y)          = neⁿᶠ (spⁿᵉ j (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y))
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ j ts xs y)      with i ≟∈ j
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ .i ts xs y)     | same   = reduce (multicutⁿᶠ (m[ i ≔ s ]⋆ⁿᶠ ts) s) (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y)
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ ._ ts xs y)     | diff j = neⁿᶠ (mspⁿᵉ j (m[ i ≔ s ]⋆ⁿᶠ ts) (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y))
  m[ i ≔ s ]ⁿᶠ lamⁿᶠ t                     = lamⁿᶠ (m[ i ≔ s ]ⁿᶠ t)
  m[ i ≔ s ]ⁿᶠ boxⁿᶠ t                     = boxⁿᶠ (m[ i ≔ s ]ⁿᶠ t)
  m[ i ≔ s ]ⁿᶠ pairⁿᶠ t u                  = pairⁿᶠ (m[ i ≔ s ]ⁿᶠ t) (m[ i ≔ s ]ⁿᶠ u)
  m[ i ≔ s ]ⁿᶠ unitⁿᶠ                      = unitⁿᶠ

  m[_≔_]ˢᵖ_ : ∀ {Ψ A B C Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ⁏ Δ ∖ i ⊢ˢᵖ B ⦙ C
  m[ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  m[ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ⁿᶠ u)
  m[ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ (m[ i ≔ s ]ˢᵖ xs)
  m[ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ (m[ i ≔ s ]ˢᵖ xs)

  m[_≔_]ᵗᵖ_ : ∀ {Ψ A B C Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ∖ i ⊢ᵗᵖ B ⦙ C
  m[ i ≔ s ]ᵗᵖ nilᵗᵖ     = nilᵗᵖ
  m[ i ≔ s ]ᵗᵖ unboxᵗᵖ u = unboxᵗᵖ u′
    where u′ = m[ pop i ≔ mmono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u

  m[_≔_]⋆ⁿᶠ : ∀ {Ξ Ψ A Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Γ ⁏ Δ ∖ i ⊢⋆ⁿᶠ Ξ
  m[_≔_]⋆ⁿᶠ {∅}     i s ∙        = ∙
  m[_≔_]⋆ⁿᶠ {Ξ , B} i s (ts , t) = m[ i ≔ s ]⋆ⁿᶠ ts , m[ i ≔ s ]ⁿᶠ t

  reduce : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ A ⦙ B → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → {{_ : Tyⁿᵉ C}} → Γ ⁏ Δ ⊢ⁿᶠ C
  reduce t                               nilˢᵖ        nilᵗᵖ       = t
  reduce (neⁿᶠ (spⁿᵉ i xs nilᵗᵖ))        nilˢᵖ        y           = neⁿᶠ (spⁿᵉ i xs y)
  reduce (neⁿᶠ (spⁿᵉ i xs (unboxᵗᵖ u)))  nilˢᵖ        y           = neⁿᶠ (spⁿᵉ i xs (unboxᵗᵖ u′))
    where u′ = reduce u nilˢᵖ (mmono⊢ᵗᵖ weak⊆ y)
  reduce (neⁿᶠ (mspⁿᵉ i ts xs nilᵗᵖ))    nilˢᵖ        y           = neⁿᶠ (mspⁿᵉ i ts xs y)
  reduce (neⁿᶠ (mspⁿᵉ i ts xs (unboxᵗᵖ u))) nilˢᵖ     y           = neⁿᶠ (mspⁿᵉ i ts xs (unboxᵗᵖ u′))
    where u′ = reduce u nilˢᵖ (mmono⊢ᵗᵖ weak⊆ y)
  reduce (neⁿᶠ t {{()}})                 (appˢᵖ xs u) y
  reduce (neⁿᶠ t {{()}})                 (fstˢᵖ xs)   y
  reduce (neⁿᶠ t {{()}})                 (sndˢᵖ xs)   y
  reduce (lamⁿᶠ t)                       (appˢᵖ xs u) y           = reduce ([ top ≔ u ]ⁿᶠ t) xs y
  reduce (boxⁿᶠ t)                       nilˢᵖ        (unboxᵗᵖ u) = m[ top ≔ t ]ⁿᶠ u
  reduce (pairⁿᶠ t u)                    (fstˢᵖ xs)   y           = reduce t xs y
  reduce (pairⁿᶠ t u)                    (sndˢᵖ xs)   y           = reduce u xs y


-- Reduction-based normal forms.

  appⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B
  appⁿᶠ (neⁿᶠ t {{()}})
  appⁿᶠ (lamⁿᶠ t) u = [ top ≔ u ]ⁿᶠ t

  multicutⁿᶠ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Ξ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ A
  multicutⁿᶠ {∅}     ∙        u = mono⊢ⁿᶠ bot⊆ u
  multicutⁿᶠ {Ξ , B} (ts , t) u = appⁿᶠ (multicutⁿᶠ ts (lamⁿᶠ u)) t

fstⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B → Γ ⁏ Δ ⊢ⁿᶠ A
fstⁿᶠ (neⁿᶠ t {{()}})
fstⁿᶠ (pairⁿᶠ t u) = t

sndⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B → Γ ⁏ Δ ⊢ⁿᶠ B
sndⁿᶠ (neⁿᶠ t {{()}})
sndⁿᶠ (pairⁿᶠ t u) = u


-- Useful equipment for deriving neutrals.

≪appˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ C ⦙ B
≪appˢᵖ nilˢᵖ        t = appˢᵖ nilˢᵖ t
≪appˢᵖ (appˢᵖ xs u) t = appˢᵖ (≪appˢᵖ xs t) u
≪appˢᵖ (fstˢᵖ xs)   t = fstˢᵖ (≪appˢᵖ xs t)
≪appˢᵖ (sndˢᵖ xs)   t = sndˢᵖ (≪appˢᵖ xs t)

≪fstˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A
≪fstˢᵖ nilˢᵖ        = fstˢᵖ nilˢᵖ
≪fstˢᵖ (appˢᵖ xs u) = appˢᵖ (≪fstˢᵖ xs) u
≪fstˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪fstˢᵖ xs)
≪fstˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪fstˢᵖ xs)

≪sndˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⁏ Δ ⊢ˢᵖ C ⦙ B
≪sndˢᵖ nilˢᵖ        = sndˢᵖ nilˢᵖ
≪sndˢᵖ (appˢᵖ xs u) = appˢᵖ (≪sndˢᵖ xs) u
≪sndˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪sndˢᵖ xs)
≪sndˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪sndˢᵖ xs)


-- Derived neutrals.

varⁿᵉ : ∀ {A Γ Δ} → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᵉ A
varⁿᵉ i = spⁿᵉ i nilˢᵖ nilᵗᵖ

appⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        t = spⁿᵉ i (≪appˢᵖ xs t) nilᵗᵖ
appⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  t = spⁿᵉ i xs (unboxᵗᵖ u′)
  where u′ = appⁿᶠ u (mmono⊢ⁿᶠ weak⊆ t)
appⁿᵉ (mspⁿᵉ i ts xs nilᵗᵖ)    t = mspⁿᵉ i ts (≪appˢᵖ xs t) nilᵗᵖ
appⁿᵉ (mspⁿᵉ i ts xs (unboxᵗᵖ u)) t = mspⁿᵉ i ts xs (unboxᵗᵖ u′)
  where u′ = appⁿᶠ u (mmono⊢ⁿᶠ weak⊆ t)

mvarⁿᵉ : ∀ {Ψ A Γ Δ} → [ Ψ ] A ∈ Δ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ψ → Γ ⁏ Δ ⊢ⁿᵉ A
mvarⁿᵉ i ts = mspⁿᵉ i ts nilˢᵖ nilᵗᵖ

fstⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪fstˢᵖ xs) nilᵗᵖ
fstⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  = spⁿᵉ i xs (unboxᵗᵖ (fstⁿᶠ u))
fstⁿᵉ (mspⁿᵉ i ts xs nilᵗᵖ)    = mspⁿᵉ i ts (≪fstˢᵖ xs) nilᵗᵖ
fstⁿᵉ (mspⁿᵉ i ts xs (unboxᵗᵖ u)) = mspⁿᵉ i ts xs (unboxᵗᵖ (fstⁿᶠ u))

sndⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪sndˢᵖ xs) nilᵗᵖ
sndⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  = spⁿᵉ i xs (unboxᵗᵖ (sndⁿᶠ u))
sndⁿᵉ (mspⁿᵉ i ts xs nilᵗᵖ)    = mspⁿᵉ i ts (≪sndˢᵖ xs) nilᵗᵖ
sndⁿᵉ (mspⁿᵉ i ts xs (unboxᵗᵖ u)) = mspⁿᵉ i ts xs (unboxᵗᵖ (sndⁿᶠ u))


-- Iterated expansion.

expand : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ⁿᶠ A
expand {α P}     t = neⁿᶠ t {{α P}}
expand {A ▻ B}   t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {[ Ψ ] A} t = neⁿᶠ t {{[ Ψ ] A}}
expand {A ∧ B}   t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))
expand {⊤}      t = unitⁿᶠ


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ Δ} → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)

mvarⁿᶠ : ∀ {Ψ A Γ Δ} → [ Ψ ] A ∈ Δ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ψ → Γ ⁏ Δ ⊢ⁿᶠ A
mvarⁿᶠ i ts = expand (mvarⁿᵉ i ts)

mutual
  unboxⁿᶠ : ∀ {Ψ A C Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ [ Ψ ] A → Γ ⁏ Δ , [ Ψ ] A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᶠ C
  unboxⁿᶠ (neⁿᶠ t)  u = expand (unboxⁿᵉ t u)
  unboxⁿᶠ (boxⁿᶠ t) u = m[ top ≔ t ]ⁿᶠ u

  unboxⁿᵉ : ∀ {Ψ A C Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ [ Ψ ] A → Γ ⁏ Δ , [ Ψ ] A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᵉ C
  unboxⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        u = spⁿᵉ i xs (unboxᵗᵖ u)
  unboxⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ t))  u = spⁿᵉ i xs (unboxᵗᵖ u′)
    where u′ = unboxⁿᶠ t (mmono⊢ⁿᶠ (keep (weak⊆)) u)
  unboxⁿᵉ (mspⁿᵉ i ts xs nilᵗᵖ)    u = mspⁿᵉ i ts xs (unboxᵗᵖ u)
  unboxⁿᵉ (mspⁿᵉ i ts xs (unboxᵗᵖ t)) u = mspⁿᵉ i ts xs (unboxᵗᵖ u′)
    where u′ = unboxⁿᶠ t (mmono⊢ⁿᶠ (keep (weak⊆)) u)


-- Translation from terms to normal forms.

mutual
  tm→nf : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
  tm→nf (var i)         = varⁿᶠ i
  tm→nf (lam t)         = lamⁿᶠ (tm→nf t)
  tm→nf (app t u)       = appⁿᶠ (tm→nf t) (tm→nf u)
  tm→nf (mvar i ts)     = mvarⁿᶠ i (tm→nf⋆ ts)
  tm→nf (box t)         = boxⁿᶠ (tm→nf t)
  tm→nf (unbox t u)     = unboxⁿᶠ (tm→nf t) (tm→nf u)
  tm→nf (pair t u)      = pairⁿᶠ (tm→nf t) (tm→nf u)
  tm→nf (fst t)         = fstⁿᶠ (tm→nf t)
  tm→nf (snd t)         = sndⁿᶠ (tm→nf t)
  tm→nf unit            = unitⁿᶠ

  tm→nf⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
  tm→nf⋆ ∙        = ∙
  tm→nf⋆ (ts , t) = tm→nf⋆ ts , tm→nf t


-- Normalisation by hereditary substitution.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = nf→tm ∘ tm→nf
