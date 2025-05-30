{-# OPTIONS --sized-types #-}

-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +.
-- Gentzen-style formalisation of syntax with context pairs.
-- Normal forms and neutrals.

module A201607.BasicILP.Syntax.DyadicGentzenNormalForm where

open import A201607.BasicILP.Syntax.DyadicGentzen public


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx² Ty Box → Ty → Set where
    neⁿᶠ   : ∀ {A Γ Δ}     → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B Γ Δ}   → Γ , A ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ▻ B

    boxⁿᶠ  : ∀ {Ψ Ω A Γ Δ} → (x : Ψ ⁏ Ω ⊢ A)
                           → Γ ⁏ Δ ⊢ⁿᶠ [ Ψ ⁏ Ω ⊢ x ] A

    pairⁿᶠ : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ : ∀ {Γ Δ}       → Γ ⁏ Δ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx² Ty Box → Ty → Set where
    varⁿᵉ   : ∀ {A Γ Δ}         → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᵉ A
    appⁿᵉ   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ⁿᵉ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᵉ B

    mvarⁿᵉ  : ∀ {Ψ Ω A x Γ Δ}   → [ Ψ ⁏ Ω ⊢ x ] A ∈ Δ
                                → Γ ⁏ Δ ⊢⋆ⁿᶠ Ψ
                                → Γ ⁏ Δ ⊢⍟ⁿᶠ Ω
                                → Γ ⁏ Δ ⊢ⁿᵉ A

    unboxⁿᵉ : ∀ {Ψ Ω A C x Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ [ Ψ ⁏ Ω ⊢ x ] A
                                → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ⁿᶠ C
                                → Γ ⁏ Δ ⊢ⁿᵉ C

    fstⁿᵉ   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ A
    sndⁿᵉ   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ B

  infix 3 _⊢⋆ⁿᶠ_
  _⊢⋆ⁿᶠ_ : Cx² Ty Box → Cx Ty → Set
  Γ ⁏ Δ ⊢⋆ⁿᶠ ∅     = 𝟙
  Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ , A = Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ × Γ ⁏ Δ ⊢ⁿᶠ A

  infix 3 _⊢⍟ⁿᶠ_
  _⊢⍟ⁿᶠ_ : Cx² Ty Box → Cx Box → Set
  Γ ⁏ Δ ⊢⍟ⁿᶠ ∅                    = 𝟙
  Γ ⁏ Δ ⊢⍟ⁿᶠ Ξ , [ Ψ ⁏ Ω ⊢ x ] A = Γ ⁏ Δ ⊢⍟ⁿᶠ Ξ × Γ ⁏ Δ ⊢ⁿᶠ [ Ψ ⁏ Ω ⊢ x ] A

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx² Ty Box → Cx Ty → Set
Γ ⁏ Δ ⊢⋆ⁿᵉ ∅     = 𝟙
Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ , A = Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ × Γ ⁏ Δ ⊢ⁿᵉ A

infix 3 _⊢⍟ⁿᵉ_
_⊢⍟ⁿᵉ_ : Cx² Ty Box → Cx Box → Set
Γ ⁏ Δ ⊢⍟ⁿᵉ ∅                    = 𝟙
Γ ⁏ Δ ⊢⍟ⁿᵉ Ξ , [ Ψ ⁏ Ω ⊢ x ] A = Γ ⁏ Δ ⊢⍟ⁿᵉ Ξ × Γ ⁏ Δ ⊢ⁿᵉ [ Ψ ⁏ Ω ⊢ x ] A


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (boxⁿᶠ t)    = box t
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit

  ne→tm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ A
  ne→tm (varⁿᵉ i)                = var i
  ne→tm (appⁿᵉ t u)              = app (ne→tm t) (nf→tm u)
  ne→tm (mvarⁿᵉ i ts us)         = mvar i (nf→tm⋆ ts) (nf→tm⍟ us)
  ne→tm (unboxⁿᵉ t u)            = unbox (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)                = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)                = snd (ne→tm t)

  nf→tm⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
  nf→tm⋆ {∅}     ∙        = ∙
  nf→tm⋆ {Ξ , A} (ts , t) = nf→tm⋆ ts , nf→tm t

  nf→tm⍟ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⍟ⁿᶠ Ξ → Γ ⁏ Δ ⊢⍟ Ξ
  nf→tm⍟ {∅}     ∙        = ∙
  nf→tm⍟ {Ξ , _} (ts , t) = nf→tm⍟ ts , nf→tm t

ne→tm⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
ne→tm⋆ {∅}     ∙        = ∙
ne→tm⋆ {Ξ , A} (ts , t) = ne→tm⋆ ts , ne→tm t

ne→tm⍟ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⍟ⁿᵉ Ξ → Γ ⁏ Δ ⊢⍟ Ξ
ne→tm⍟ {∅}     ∙        = ∙
ne→tm⍟ {Ξ , _} (ts , t) = ne→tm⍟ ts , ne→tm t


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ⁿᶠ A → Γ′ ⁏ Δ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (boxⁿᶠ t)    = boxⁿᶠ t
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ⁿᵉ A → Γ′ ⁏ Δ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)                = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u)              = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (mvarⁿᵉ i ts us)         = mvarⁿᵉ i (mono⊢⋆ⁿᶠ η ts) (mono⊢⍟ⁿᶠ η us)
  mono⊢ⁿᵉ η (unboxⁿᵉ t u)            = unboxⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)                = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)                = sndⁿᵉ (mono⊢ⁿᵉ η t)

  mono⊢⋆ⁿᶠ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Γ′ ⁏ Δ ⊢⋆ⁿᶠ Ξ
  mono⊢⋆ⁿᶠ {∅}     η ∙        = ∙
  mono⊢⋆ⁿᶠ {Ξ , A} η (ts , t) = mono⊢⋆ⁿᶠ η ts , mono⊢ⁿᶠ η t

  mono⊢⍟ⁿᶠ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⍟ⁿᶠ Ξ → Γ′ ⁏ Δ ⊢⍟ⁿᶠ Ξ
  mono⊢⍟ⁿᶠ {∅}     η ∙        = ∙
  mono⊢⍟ⁿᶠ {Ξ , _} η (ts , t) = mono⊢⍟ⁿᶠ η ts , mono⊢ⁿᶠ η t

mono⊢⋆ⁿᵉ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ′ ⁏ Δ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ {∅}     η ∙        = ∙
mono⊢⋆ⁿᵉ {Ξ , A} η (ts , t) = mono⊢⋆ⁿᵉ η ts , mono⊢ⁿᵉ η t

mono⊢⍟ⁿᵉ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⍟ⁿᵉ Ξ → Γ′ ⁏ Δ ⊢⍟ⁿᵉ Ξ
mono⊢⍟ⁿᵉ {∅}     η ∙        = ∙
mono⊢⍟ⁿᵉ {Ξ , _} η (ts , t) = mono⊢⍟ⁿᵉ η ts , mono⊢ⁿᵉ η t


-- Monotonicity with respect to modal context inclusion.

mutual
  mmono⊢ⁿᶠ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ′ ⊢ⁿᶠ A
  mmono⊢ⁿᶠ θ (neⁿᶠ t)     = neⁿᶠ (mmono⊢ⁿᵉ θ t)
  mmono⊢ⁿᶠ θ (lamⁿᶠ t)    = lamⁿᶠ (mmono⊢ⁿᶠ θ t)
  mmono⊢ⁿᶠ θ (boxⁿᶠ t)    = boxⁿᶠ t
  mmono⊢ⁿᶠ θ (pairⁿᶠ t u) = pairⁿᶠ (mmono⊢ⁿᶠ θ t) (mmono⊢ⁿᶠ θ u)
  mmono⊢ⁿᶠ θ unitⁿᶠ       = unitⁿᶠ

  mmono⊢ⁿᵉ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ′ ⊢ⁿᵉ A
  mmono⊢ⁿᵉ θ (varⁿᵉ i)                = varⁿᵉ i
  mmono⊢ⁿᵉ θ (appⁿᵉ t u)              = appⁿᵉ (mmono⊢ⁿᵉ θ t) (mmono⊢ⁿᶠ θ u)
  mmono⊢ⁿᵉ θ (mvarⁿᵉ i ts us)         = mvarⁿᵉ (mono∈ θ i) (mmono⊢⋆ⁿᶠ θ ts) (mmono⊢⍟ⁿᶠ θ us)
  mmono⊢ⁿᵉ θ (unboxⁿᵉ t u)            = unboxⁿᵉ (mmono⊢ⁿᵉ θ t) (mmono⊢ⁿᶠ (keep θ) u)
  mmono⊢ⁿᵉ θ (fstⁿᵉ t)                = fstⁿᵉ (mmono⊢ⁿᵉ θ t)
  mmono⊢ⁿᵉ θ (sndⁿᵉ t)                = sndⁿᵉ (mmono⊢ⁿᵉ θ t)

  mmono⊢⋆ⁿᶠ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ → Γ ⁏ Δ′ ⊢⋆ⁿᶠ Ξ
  mmono⊢⋆ⁿᶠ {∅}     θ ∙        = ∙
  mmono⊢⋆ⁿᶠ {Ξ , A} θ (ts , t) = mmono⊢⋆ⁿᶠ θ ts , mmono⊢ⁿᶠ θ t

  mmono⊢⍟ⁿᶠ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⍟ⁿᶠ Ξ → Γ ⁏ Δ′ ⊢⍟ⁿᶠ Ξ
  mmono⊢⍟ⁿᶠ {∅}     θ ∙        = ∙
  mmono⊢⍟ⁿᶠ {Ξ , _} θ (ts , t) = mmono⊢⍟ⁿᶠ θ ts , mmono⊢ⁿᶠ θ t

mmono⊢⋆ⁿᵉ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ′ ⊢⋆ⁿᵉ Ξ
mmono⊢⋆ⁿᵉ {∅}     θ ∙        = ∙
mmono⊢⋆ⁿᵉ {Ξ , A} θ (ts , t) = mmono⊢⋆ⁿᵉ θ ts , mmono⊢ⁿᵉ θ t

mmono⊢⍟ⁿᵉ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⍟ⁿᵉ Ξ → Γ ⁏ Δ′ ⊢⍟ⁿᵉ Ξ
mmono⊢⍟ⁿᵉ {∅}     θ ∙        = ∙
mmono⊢⍟ⁿᵉ {Ξ , _} θ (ts , t) = mmono⊢⍟ⁿᵉ θ ts , mmono⊢ⁿᵉ θ t


-- Monotonicity using context pairs.

mono²⊢ⁿᶠ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ⁿᶠ A → Π′ ⊢ⁿᶠ A
mono²⊢ⁿᶠ (η , θ) = mono⊢ⁿᶠ η ∘ mmono⊢ⁿᶠ θ

mono²⊢ⁿᵉ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ⁿᵉ A → Π′ ⊢ⁿᵉ A
mono²⊢ⁿᵉ (η , θ) = mono⊢ⁿᵉ η ∘ mmono⊢ⁿᵉ θ


-- Generalised reflexivity.

refl⊢⋆ⁿᵉ : ∀ {Γ Ψ Δ} → {{_ : Ψ ⊆ Γ}} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ψ
refl⊢⋆ⁿᵉ {∅}     {{done}}   = ∙
refl⊢⋆ⁿᵉ {Γ , A} {{skip η}} = mono⊢⋆ⁿᵉ weak⊆ (refl⊢⋆ⁿᵉ {{η}})
refl⊢⋆ⁿᵉ {Γ , A} {{keep η}} = mono⊢⋆ⁿᵉ weak⊆ (refl⊢⋆ⁿᵉ {{η}}) , varⁿᵉ top
