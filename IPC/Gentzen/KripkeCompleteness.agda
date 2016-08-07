module IPC.Gentzen.KripkeCompleteness where

open import IPC.Gentzen.KripkeSoundness public


-- Derivations, as Gentzen-style natural deduction trees.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    ttⁿᶠ   : Γ ⊢ⁿᶠ ⊤
    inlⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A ∨ B
    inrⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∨ B

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ  : ∀ {A}     → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
    boomⁿᵉ : ∀ {C}     → Γ ⊢ⁿᵉ ⊥ → Γ ⊢ⁿᵉ C
    caseⁿᵉ : ∀ {A B C} → Γ ⊢ⁿᵉ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C

infix 3 _⊢⋆ⁿᶠ_
_⊢⋆ⁿᶠ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᶠ ⌀     = 𝟙
Γ ⊢⋆ⁿᶠ Π , A = Γ ⊢⋆ⁿᶠ Π × Γ ⊢ⁿᶠ A

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᵉ ⌀     = 𝟙
Γ ⊢⋆ⁿᵉ Π , A = Γ ⊢⋆ⁿᵉ Π × Γ ⊢ⁿᵉ A


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm ttⁿᶠ         = tt
  nf→tm (inlⁿᶠ t)    = inl (nf→tm t)
  nf→tm (inrⁿᶠ t)    = inr (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)      = var i
  ne→tm (appⁿᵉ t u)    = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)      = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)      = snd (ne→tm t)
  ne→tm (boomⁿᵉ t)     = boom (ne→tm t)
  ne→tm (caseⁿᵉ t u v) = case (ne→tm t) (nf→tm u) (nf→tm v)

nf→tm⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᶠ Π → Γ ⊢⋆ Π
nf→tm⋆ {⌀}     ∙        = ∙
nf→tm⋆ {Π , A} (ts , t) = nf→tm⋆ ts , nf→tm t

ne→tm⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᵉ Π → Γ ⊢⋆ Π
ne→tm⋆ {⌀}     ∙        = ∙
ne→tm⋆ {Π , A} (ts , t) = ne→tm⋆ ts , ne→tm t


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η ttⁿᶠ         = ttⁿᶠ
  mono⊢ⁿᶠ η (inlⁿᶠ t)    = inlⁿᶠ (mono⊢ⁿᶠ η t)
  mono⊢ⁿᶠ η (inrⁿᶠ t)    = inrⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)      = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u)    = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)      = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)      = sndⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (boomⁿᵉ t)     = boomⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (caseⁿᵉ t u v) = caseⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ (keep η) u) (mono⊢ⁿᶠ (keep η) v)

mono⊢⋆ⁿᶠ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᶠ Π → Γ′ ⊢⋆ⁿᶠ Π
mono⊢⋆ⁿᶠ {⌀}     η ∙        = ∙
mono⊢⋆ⁿᶠ {Π , A} η (ts , t) = mono⊢⋆ⁿᶠ η ts , mono⊢ⁿᶠ η t

mono⊢⋆ⁿᵉ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᵉ Π → Γ′ ⊢⋆ⁿᵉ Π
mono⊢⋆ⁿᵉ {⌀}     η ∙        = ∙
mono⊢⋆ⁿᵉ {Π , A} η (ts , t) = mono⊢⋆ⁿᵉ η ts , mono⊢ⁿᵉ η t




-- Using CPS forcing, following Ilik.

module IlikCompleteness where
  open IlikSoundness public


  -- The canonical model.

  instance
    canon : Model
    canon = record
      { World   = Cx Ty
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      ; _⊪ᵅ_   = λ Γ P → Γ ⊢ⁿᵉ α P
      ; mono⊪ᵅ = mono⊢ⁿᵉ
      ; _‼_     = λ Γ A → Γ ⊢ⁿᶠ A
      }


  -- Soundness and completeness with respect to the canonical model.

  mutual
    reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
    reflect {α P}   t = return {α P} t
    reflect {A ▻ B} t = return {A ▻ B} (λ η a → reflect {B} (appⁿᵉ (mono⊢ⁿᵉ η t) (reify {A} a)))
    reflect {A ∧ B} t = return {A ∧ B} (reflect {A} (fstⁿᵉ t) , reflect {B} (sndⁿᵉ t))
    reflect {⊤}    t = return {⊤} ∙
    reflect {⊥}    t = λ η k → neⁿᶠ (boomⁿᵉ (mono⊢ⁿᵉ η t))
    reflect {A ∨ B} t = λ η k → neⁿᶠ (caseⁿᵉ (mono⊢ⁿᵉ η t)
                                        (k weak⊆ (ι₁ (reflect {A} (varⁿᵉ top))))
                                        (k weak⊆ (ι₂ (reflect {B} (varⁿᵉ top)))))

    reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
    reify {α P}   k = k refl≤ (λ η s → neⁿᶠ s)
    reify {A ▻ B} k = k refl≤ (λ η s → lamⁿᶠ (reify {B} (s weak⊆ (reflect {A} (varⁿᵉ top)))))
    reify {A ∧ B} k = k refl≤ (λ η s → pairⁿᶠ (reify {A} (π₁ s)) (reify {B} (π₂ s)))
    reify {⊤}    k = k refl≤ (λ η s → ttⁿᶠ)
    reify {⊥}    k = k refl≤ (λ η ())
    reify {A ∨ B} k = k refl≤ (λ η s → elim⊎ s
                                          (λ a → inlⁿᶠ (reify {A} (λ η′ k′ → a η′ k′)))
                                          (λ b → inrⁿᶠ (reify {B} (λ η′ k′ → b η′ k′))))

  reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᵉ Π → Γ ⊩⋆ Π
  reflect⋆ {⌀}     ∙        = ∙
  reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

  reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ⁿᶠ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


  -- Reflexivity and transitivity.

  refl⊢⋆ⁿᵉ : ∀ {Γ} → Γ ⊢⋆ⁿᵉ Γ
  refl⊢⋆ⁿᵉ {⌀}     = ∙
  refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ weak⊆ refl⊢⋆ⁿᵉ , varⁿᵉ top

  refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
  refl⊩⋆ = reflect⋆ refl⊢⋆ⁿᵉ

  trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
  trans⊩⋆ ts us = eval⋆ (trans⊢⋆ (nf→tm⋆ (reify⋆ ts)) (nf→tm⋆ (reify⋆ us))) refl⊩⋆


  -- Completeness, or quotation.

  quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
  quot t = nf→tm (reify (t refl⊩⋆))


  -- Normalisation by evaluation.

  norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
  norm = quot ∘ eval
