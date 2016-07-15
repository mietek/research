module BasicIPC.Gentzen.KripkeSemantics.Completeness where

open import BasicIPC.Gentzen.KripkeSemantics.Core public


-- Derivations, as Gentzen-style natural deduction trees.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▷ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    ttⁿᶠ   : Γ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ : ∀ {A}   → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm ttⁿᶠ         = tt

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)   = var i
  ne→tm (appⁿᵉ t u) = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)   = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)   = snd (ne→tm t)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η ttⁿᶠ         = ttⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)   = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u) = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)   = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)   = sndⁿᵉ (mono⊢ⁿᵉ η t)


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᵅ_   = λ Γ P → Γ ⊢ⁿᵉ α P
    ; mono⊩ᵅ = mono⊢ⁿᵉ
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} (appⁿᵉ (mono⊢ⁿᵉ ξ t) (reify {A} a))
  reflect {A ∧ B} t = ᴬpair (reflect {A} (fstⁿᵉ t)) (reflect {B} (sndⁿᵉ t))
  reflect {⊤}    t = ᴬtt

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {α P}   s = neⁿᶠ s
  reify {A ▷ B} s = lamⁿᶠ (reify {B} (s weak⊆ (reflect {A} (varⁿᵉ top))))
  reify {A ∧ B} s = pairⁿᶠ (reify {A} (ᴬfst s)) (reify {B} (ᴬsnd s))
  reify {⊤}    s = ttⁿᶠ

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬtt
refl⊩⋆ {Γ , A} = ᴬpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} (varⁿᵉ top))


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = nf→tm (reify (t refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
