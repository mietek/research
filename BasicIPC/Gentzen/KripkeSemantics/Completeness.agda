module BasicIPC.Gentzen.KripkeSemantics.Completeness where

open import BasicIPC.Gentzen.KripkeSemantics.Core public


-- Normal forms and neutrals.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▷ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ⫪
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ : ∀ {A}   → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B


-- Translation to terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm unitⁿᶠ       = unit
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)

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
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)

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
    ; _⊩ᴬ_   = λ Γ P → Γ ⊢ⁿᵉ ᴬ P
    ; mono⊩ᴬ = mono⊢ⁿᵉ
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {ᴬ P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} (appⁿᵉ (mono⊢ⁿᵉ ξ t) (reify {A} a))
  reflect {⫪}    t = tt
  reflect {A ∧ B} t = reflect {A} (fstⁿᵉ t) ∙ reflect {B} (sndⁿᵉ t)

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {ᴬ P}   s       = neⁿᶠ s
  reify {A ▷ B} f       = lamⁿᶠ (reify {B} (f weak⊆ (reflect {A} (varⁿᵉ top))))
  reify {⫪}    tt      = unitⁿᶠ
  reify {A ∧ B} (a ∙ b) = pairⁿᶠ (reify {A} a) (reify {B} b)

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = tt
refl⊩⋆ {Γ , A} = mono⊩⋆ {Γ} weak⊆ refl⊩⋆ ∙ reflect {A} (varⁿᵉ top)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = nf→tm (reify (t refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
