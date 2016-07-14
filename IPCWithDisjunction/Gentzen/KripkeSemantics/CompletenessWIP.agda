module IPCWithDisjunction.Gentzen.KripkeSemantics.CompletenessWIP where

open import IPCWithDisjunction.Gentzen.KripkeSemantics.Core public


-- Normal forms and neutrals.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▷ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ⫪
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    inlⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A ∨ B
    inrⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∨ B

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ  : ∀ {A}     → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
    caseⁿᵉ : ∀ {A B C} → Γ ⊢ⁿᵉ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C


-- Translation to terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm unitⁿᶠ       = unit
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm (inlⁿᶠ t)    = inl (nf→tm t)
  nf→tm (inrⁿᶠ t)    = inr (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)      = var i
  ne→tm (appⁿᵉ t u)    = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)      = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)      = snd (ne→tm t)
  ne→tm (caseⁿᵉ t u v) = case (ne→tm t) (nf→tm u) (nf→tm v)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η (inlⁿᶠ t)    = inlⁿᶠ (mono⊢ⁿᶠ η t)
  mono⊢ⁿᶠ η (inrⁿᶠ t)    = inrⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)      = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u)    = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)      = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)      = sndⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (caseⁿᵉ t u v) = caseⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ (keep η) u) (mono⊢ⁿᶠ (keep η) v)


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊪ᴬ_   = λ Γ P → Γ ⊢ⁿᵉ ᴬ P
    ; mono⊪ᴬ = mono⊢ⁿᵉ
    ; _⁂_    = λ Γ A → Γ ⊢ⁿᵉ A
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {ᴬ P}   t = return {ᴬ P} t
  reflect {A ▷ B} t = return {A ▷ B} (λ ξ a → reflect {B} (appⁿᵉ (mono⊢ⁿᵉ ξ t) (reify {A} a)))
  reflect {⫪}    t = return {⫪} tt
  reflect {A ∧ B} t = return {A ∧ B} (reflect {A} (fstⁿᵉ t) ∙ reflect {B} (sndⁿᵉ t))
  reflect {A ∨ B} t = λ ξ k → caseⁿᵉ (mono⊢ⁿᵉ ξ t)
                                 (neⁿᶠ (k weak⊆ (inj₁ (reflect {A} (varⁿᵉ top)))))
                                 (neⁿᶠ (k weak⊆ (inj₂ (reflect {B} (varⁿᵉ top)))))

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {ᴬ P}   k = neⁿᶠ (k refl≤ (λ ξ s → s))
  reify {A ▷ B} k = {!!}
  reify {⫪}    k = {!!}
  reify {A ∧ B} k = {!!}
  reify {A ∨ B} k = {!!}

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = tt
refl⊩⋆ {Γ , A} = mono⊩⋆ {Γ} weak⊆ refl⊩⋆ ∙ reflect {A} (varⁿᵉ top)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = nf→tm (reify (t refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
