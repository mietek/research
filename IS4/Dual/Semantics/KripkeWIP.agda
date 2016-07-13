module IS4.Dual.Semantics.KripkeWIP where

open import IS4.Dual.Gentzen public


-- Non-standard intuitionistic modal Kripke models, based on Marti and Studer.

record Model : Set₁ where
  infix 3 _≤_ _R_ _⊩ᴬ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Modal accessibility; preorder.
    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- Forcing for atomic propositions; monotonic with respect to intuitionistic accessibility.
    _⊩ᴬ_   : World → Atom → Set
    mono⊩ᴬ : ∀ {w w′ p} → w ≤ w′ → w ⊩ᴬ p → w′ ⊩ᴬ p

    -- Modal accessibility is ??? with respect to intuitionistic accessibility;
    -- seems odd, but appears in Ono; repeated by Marti and Studer.
    fnordR : ∀ {w w′ w″} → w ≤ w′ → w′ R w″ → w R w″

    -- NEW: Forcing is monotonic with respect to modal accessibility; needed for soundness proof;
    -- seems OK.
    mmono⊩ᴬ : ∀ {w w′ p} → w R w′ → w ⊩ᴬ p → w′ ⊩ᴬ p

    -- NEW: Intuitionistic accessibility is ??? with respect to modal accessibility;
    -- needed for soundness proof; seems odd.
    mfnord≤ : ∀ {w w′ w″} → w R w′ → w′ ≤ w″ → w ≤ w″

  -- Intuitionistic accessibility implies modal accessibility; appears in Ono as frame condition.
  ≤→R : ∀ {w w′} → w ≤ w′ → w R w′
  ≤→R ξ = fnordR ξ reflR

  -- Modal accessibility implies intuitionistic accessibility; seems odd.
  R→≤ : ∀ {w w′} → w R w′ → w ≤ w′
  R→≤ ζ = mfnord≤ ζ refl≤

open Model {{…}} public


-- Truth in one model.

module _ {{_ : Model}} where
  infix 3 _⊩ᵀ_
  _⊩ᵀ_ : World → Ty → Set
  w ⊩ᵀ ᴬ P   = w ⊩ᴬ P
  w ⊩ᵀ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ᵀ A → w′ ⊩ᵀ B
  w ⊩ᵀ □ A   = ∀ {w′} → w R w′ → w′ ⊩ᵀ A
  w ⊩ᵀ ⫪    = ⊤
  w ⊩ᵀ A ∧ B = w ⊩ᵀ A × w ⊩ᵀ B

  infix 3 _⊩ᴳ_
  _⊩ᴳ_ : World → Cx Ty → Set
  w ⊩ᴳ ⌀     = ⊤
  w ⊩ᴳ Γ , A = w ⊩ᴳ Γ × w ⊩ᵀ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ᵀ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mono⊩ᵀ {ᴬ P}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ᵀ {A ▷ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵀ {□ A}   ξ f       = λ ζ → f (fnordR ξ ζ)
  mono⊩ᵀ {⫪}    ξ tt      = tt
  mono⊩ᵀ {A ∧ B} ξ (a ∙ b) = mono⊩ᵀ {A} ξ a ∙ mono⊩ᵀ {B} ξ b

  mono⊩ᴳ : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᴳ Γ → w′ ⊩ᴳ Γ
  mono⊩ᴳ {⌀}     ξ tt      = tt
  mono⊩ᴳ {Γ , A} ξ (γ ∙ a) = mono⊩ᴳ {Γ} ξ γ ∙ mono⊩ᵀ {A} ξ a


  -- Monotonicity with respect to modal accessibility.

  mmono⊩ᵀ : ∀ {A w w′} → w R w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mmono⊩ᵀ {ᴬ P}   ζ s       = mmono⊩ᴬ ζ s
  mmono⊩ᵀ {A ▷ B} ζ f       = λ ξ a → f (mfnord≤ ζ ξ) a
  mmono⊩ᵀ {□ A}   ζ f       = λ ζ′ → f (transR ζ ζ′)
  mmono⊩ᵀ {⫪}    ζ tt      = tt
  mmono⊩ᵀ {A ∧ B} ζ (a ∙ b) = mmono⊩ᵀ {A} ζ a ∙ mmono⊩ᵀ {B} ζ b

  mmono⊩ᴳ : ∀ {Δ w w′} → w R w′ → w ⊩ᴳ Δ → w′ ⊩ᴳ Δ
  mmono⊩ᴳ {⌀}     ζ tt      = tt
  mmono⊩ᴳ {Δ , A} ζ (δ ∙ a) = mmono⊩ᴳ {Δ} ζ δ ∙ mmono⊩ᵀ {A} ζ a


-- Truth in all models.

infix 3 _⨾_⊩_
_⨾_⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᴳ Γ → w ⊩ᴳ Δ → w ⊩ᵀ A


-- Soundness with respect to all models, or evaluation.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ⊩ A
lookup top     (γ ∙ a) δ = a
lookup (pop i) (γ ∙ b) δ = lookup i γ δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ⊩ A
mlookup top     γ (δ ∙ a) = a
mlookup (pop i) γ (δ ∙ b) = mlookup i γ δ

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩ᴳ ξ γ ∙ a) (mono⊩ᴳ ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t tt (mmono⊩ᴳ ζ δ)
eval (unbox t u) γ δ = eval u γ (δ ∙ (eval t γ δ) reflR)
eval unit        γ δ = tt
eval (pair t u)  γ δ = eval t γ δ ∙ eval u γ δ
eval (fst t)     γ δ with eval t γ δ
…                   | a ∙ b = a
eval (snd t)     γ δ with eval t γ δ
…                   | a ∙ b = b


-- Canonical model.

Cx² : Set → Set
Cx² U = Cx U × Cx U

module _ {U : Set} where
  infix 3 _⊆²_
  _⊆²_ : Cx² U → Cx² U → Set
  (Γ ∙ Δ) ⊆² (Γ′ ∙ Δ′) = (Γ ⊆ Γ′) × (Δ ⊆ Δ′)

  refl⊆² : ∀ {Ξ} → Ξ ⊆² Ξ
  refl⊆² = refl⊆ ∙ refl⊆

  trans⊆² : ∀ {Ξ Ξ′ Ξ″} → Ξ ⊆² Ξ′ → Ξ′ ⊆² Ξ″ → Ξ ⊆² Ξ″
  trans⊆² (η ∙ θ) (η′ ∙ θ′) = trans⊆ η η′ ∙ trans⊆ θ θ′

  infix 3 _R²_
  data _R²_ : Cx² U → Cx² U → Set where
    step : ∀ {Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → (Γ ∙ Δ) R² (Γ′ ∙ Δ′)
    jump : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → (⌀ ∙ Δ) R² (Γ ∙ Δ′)

  ⊆²→R² : ∀ {Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ R² Ξ′
  ⊆²→R² (η ∙ θ) = step η θ

  R²→⊆² : ∀ {Ξ Ξ′} → Ξ R² Ξ′ → Ξ ⊆² Ξ′
  R²→⊆² (step η θ) = η ∙ θ
  R²→⊆² (jump θ)   = bot⊆ ∙ θ

  reflR² : ∀ {Ξ} → Ξ R² Ξ
  reflR² = step refl⊆ refl⊆

  transR² : ∀ {Ξ Ξ′ Ξ″} → Ξ R² Ξ′ → Ξ′ R² Ξ″ → Ξ R² Ξ″
  transR² (step η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  transR² (step η θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)
  transR² (jump θ)   (step η′ θ′) = jump (trans⊆ θ θ′)
  transR² (jump θ)   (jump θ′)    = jump (trans⊆ θ θ′)

  fnordR² : ∀ {X Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ′ R² X → Ξ R² X
  fnordR² (η ∙ θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  fnordR² (η ∙ θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)

  mfnord⊆² : ∀ {X Ξ Ξ′} → Ξ R² Ξ′ → Ξ′ ⊆² X → Ξ ⊆² X
  mfnord⊆² (step η θ) (η′ ∙ θ′) = trans⊆ η η′ ∙ trans⊆ θ θ′
  mfnord⊆² (jump θ)   (η′ ∙ θ′) = bot⊆ ∙ trans⊆ θ θ′

infix 3 _⊢²_
_⊢²_ : Cx² Ty → Ty → Set
(Γ ∙ Δ) ⊢² A = Γ ⨾ Δ ⊢ A

mono⊢² : ∀ {A Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ ⊢² A → Ξ′ ⊢² A
mono⊢² (η ∙ θ) = mono⊢ η ∘ mmono⊢ θ

mmono⊢² : ∀ {A Ξ Ξ′} → Ξ R² Ξ′ → Ξ ⊢² A → Ξ′ ⊢² A
mmono⊢² (step η θ) = mono⊢ η ∘ mmono⊢ θ
mmono⊢² (jump θ)   = mono⊢ bot⊆ ∘ mmono⊢ θ

instance
  canon : Model
  canon = record
    { World    = Cx² Ty
    ; _≤_      = _⊆²_
    ; refl≤    = refl⊆²
    ; trans≤   = trans⊆²
    ; _R_      = _R²_
    ; reflR    = reflR²
    ; transR   = transR²
    ; _⊩ᴬ_    = λ { Ξ P → Ξ ⊢² ᴬ P }
    ; mono⊩ᴬ  = mono⊢²
    ; fnordR   = fnordR²
    ; mmono⊩ᴬ = mmono⊢²
    ; mfnord≤  = mfnord⊆²
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (Γ ∙ Δ) ⊩ᵀ A
  reflect {ᴬ P}   t = t
  reflect {A ▷ B} t = λ { {Γ′ ∙ Δ′} (η ∙ θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (Γ ∙ Δ) R² (Γ′ ∙ Δ′) → (Γ′ ∙ Δ′) ⊩ᵀ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ bot⊆ (mmono⊢ θ t)) mv₀)
  reflect {⫪}    t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ᵀ A → Γ ⨾ Δ ⊢ A
  reify {ᴬ P}   s       = s
  reify {A ▷ B} f       = lam (reify {B} (f (weak⊆ ∙ refl⊆) (reflect {A} v₀)))
  reify {□ A}   f       = box (reify {A} (f {!jump ?!}))
  reify {⫪}    tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᴳ : ∀ {Γ Δ} → (Γ ∙ Δ) ⊩ᴳ Γ
refl⊩ᴳ {⌀}     = tt
refl⊩ᴳ {Γ , A} = mono⊩ᴳ {Γ} (weak⊆ ∙ refl⊆) refl⊩ᴳ ∙ reflect {A} v₀

mrefl⊩ᴳ : ∀ {Δ Γ} → (Γ ∙ Δ) ⊩ᴳ Δ
mrefl⊩ᴳ {⌀}     = tt
mrefl⊩ᴳ {Δ , A} = mmono⊩ᴳ {Δ} (step refl⊆ weak⊆) mrefl⊩ᴳ ∙ reflect {A} mv₀


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩ᴳ mrefl⊩ᴳ)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
