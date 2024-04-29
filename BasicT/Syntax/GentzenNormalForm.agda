-- TODO
-- Gentzen-style formalisation of syntax.
-- Normal forms and neutrals.

module A201607.BasicT.Syntax.GentzenNormalForm where

open import A201607.BasicT.Syntax.Gentzen public


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ    : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ   : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ  : Γ ⊢ⁿᶠ ⊤
    trueⁿᶠ  : Γ ⊢ⁿᶠ BOOL
    falseⁿᶠ : Γ ⊢ⁿᶠ BOOL
    zeroⁿᶠ  : Γ ⊢ⁿᶠ NAT
    sucⁿᶠ   : Γ ⊢ⁿᶠ NAT → Γ ⊢ⁿᶠ NAT

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ : ∀ {A}   → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
    ifⁿᵉ  : ∀ {C}   → Γ ⊢ⁿᵉ BOOL → Γ ⊢ⁿᶠ C → Γ ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C
    itⁿᵉ  : ∀ {C}   → Γ ⊢ⁿᵉ NAT → Γ ⊢ⁿᶠ C ▻ C → Γ ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C
    recⁿᵉ : ∀ {C}   → Γ ⊢ⁿᵉ NAT → Γ ⊢ⁿᶠ NAT ▻ C ▻ C → Γ ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C

infix 3 _⊢⋆ⁿᶠ_
_⊢⋆ⁿᶠ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᶠ ∅     = 𝟙
Γ ⊢⋆ⁿᶠ Ξ , A = Γ ⊢⋆ⁿᶠ Ξ × Γ ⊢ⁿᶠ A

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᵉ ∅     = 𝟙
Γ ⊢⋆ⁿᵉ Ξ , A = Γ ⊢⋆ⁿᵉ Ξ × Γ ⊢ⁿᵉ A


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit
  nf→tm trueⁿᶠ       = true
  nf→tm falseⁿᶠ      = true
  nf→tm zeroⁿᶠ       = zero
  nf→tm (sucⁿᶠ t)    = suc (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)     = var i
  ne→tm (appⁿᵉ t u)   = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)     = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)     = snd (ne→tm t)
  ne→tm (ifⁿᵉ t u v)  = if (ne→tm t) (nf→tm u) (nf→tm v)
  ne→tm (itⁿᵉ t u v)  = it (ne→tm t) (nf→tm u) (nf→tm v)
  ne→tm (recⁿᵉ t u v) = rec (ne→tm t) (nf→tm u) (nf→tm v)

nf→tm⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ⁿᶠ Ξ → Γ ⊢⋆ Ξ
nf→tm⋆ {∅}     ∙        = ∙
nf→tm⋆ {Ξ , A} (ts , t) = nf→tm⋆ ts , nf→tm t

ne→tm⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ⁿᵉ Ξ → Γ ⊢⋆ Ξ
ne→tm⋆ {∅}     ∙        = ∙
ne→tm⋆ {Ξ , A} (ts , t) = ne→tm⋆ ts , ne→tm t


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η trueⁿᶠ       = trueⁿᶠ
  mono⊢ⁿᶠ η falseⁿᶠ      = trueⁿᶠ
  mono⊢ⁿᶠ η zeroⁿᶠ       = zeroⁿᶠ
  mono⊢ⁿᶠ η (sucⁿᶠ t)    = sucⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)     = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u)   = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)     = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)     = sndⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (ifⁿᵉ t u v)  = ifⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u) (mono⊢ⁿᶠ η v)
  mono⊢ⁿᵉ η (itⁿᵉ t u v)  = itⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u) (mono⊢ⁿᶠ η v)
  mono⊢ⁿᵉ η (recⁿᵉ t u v) = recⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u) (mono⊢ⁿᶠ η v)

mono⊢⋆ⁿᶠ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᶠ Ξ → Γ′ ⊢⋆ⁿᶠ Ξ
mono⊢⋆ⁿᶠ {∅}     η ∙        = ∙
mono⊢⋆ⁿᶠ {Ξ , A} η (ts , t) = mono⊢⋆ⁿᶠ η ts , mono⊢ⁿᶠ η t

mono⊢⋆ⁿᵉ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᵉ Ξ → Γ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ {∅}     η ∙        = ∙
mono⊢⋆ⁿᵉ {Ξ , A} η (ts , t) = mono⊢⋆ⁿᵉ η ts , mono⊢ⁿᵉ η t


-- Reflexivity.

refl⊢⋆ⁿᵉ : ∀ {Γ} → Γ ⊢⋆ⁿᵉ Γ
refl⊢⋆ⁿᵉ {∅}     = ∙
refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ weak⊆ refl⊢⋆ⁿᵉ , varⁿᵉ top
