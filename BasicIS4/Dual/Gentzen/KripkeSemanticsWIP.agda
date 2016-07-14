module BasicIS4.Dual.Gentzen.KripkeSemanticsWIP where

open import BasicIS4.Dual.Gentzen.Core public


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

    -- NEW: Forcing is monotonic with respect to modal accessibility; needed for soundness;
    -- seems OK.
    mmono⊩ᴬ : ∀ {w w′ p} → w R w′ → w ⊩ᴬ p → w′ ⊩ᴬ p

    -- NEW: Intuitionistic accessibility is ??? with respect to modal accessibility;
    -- needed for soundness; seems odd.
    mfnord≤ : ∀ {w w′ w″} → w R w′ → w′ ≤ w″ → w ≤ w″

  -- Intuitionistic accessibility implies modal accessibility; appears in Ono as frame condition.
  ≤→R : ∀ {w w′} → w ≤ w′ → w R w′
  ≤→R ξ = fnordR ξ reflR

  -- Modal accessibility implies intuitionistic accessibility; seems odd.
  R→≤ : ∀ {w w′} → w R w′ → w ≤ w′
  R→≤ ζ = mfnord≤ ζ refl≤

open Model {{…}} public


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ ᴬ P   = w ⊩ᴬ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A   = ∀ {w′} → w R w′ → w′ ⊩ A
  w ⊩ ⫪    = ⊤
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {ᴬ P}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ {A ▷ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ f       = λ ζ → f (fnordR ξ ζ)
  mono⊩ {⫪}    ξ tt      = tt
  mono⊩ {A ∧ B} ξ (a ∙ b) = mono⊩ {A} ξ a ∙ mono⊩ {B} ξ b

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ tt      = tt
  mono⊩⋆ {Γ , A} ξ (γ ∙ a) = mono⊩⋆ {Γ} ξ γ ∙ mono⊩ {A} ξ a


  -- Monotonicity with respect to modal accessibility.

  mmono⊩ : ∀ {A w w′} → w R w′ → w ⊩ A → w′ ⊩ A
  mmono⊩ {ᴬ P}   ζ s       = mmono⊩ᴬ ζ s
  mmono⊩ {A ▷ B} ζ f       = λ ξ a → f (mfnord≤ ζ ξ) a
  mmono⊩ {□ A}   ζ f       = λ ζ′ → f (transR ζ ζ′)
  mmono⊩ {⫪}    ζ tt      = tt
  mmono⊩ {A ∧ B} ζ (a ∙ b) = mmono⊩ {A} ζ a ∙ mmono⊩ {B} ζ b

  mmono⊩⋆ : ∀ {Δ w w′} → w R w′ → w ⊩⋆ Δ → w′ ⊩⋆ Δ
  mmono⊩⋆ {⌀}     ζ tt      = tt
  mmono⊩⋆ {Δ , A} ζ (δ ∙ a) = mmono⊩⋆ {Δ} ζ δ ∙ mmono⊩ {A} ζ a


-- Forcing in all models.

infix 3 _⨾_ᴹ⊩_
_⨾_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Δ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ᴹ⊩ A
lookup top     (γ ∙ a) δ = a
lookup (pop i) (γ ∙ b) δ = lookup i γ δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ᴹ⊩ A
mlookup top     γ (δ ∙ a) = a
mlookup (pop i) γ (δ ∙ b) = mlookup i γ δ

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ᴹ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ ∙ a) (mono⊩⋆ ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t tt (mmono⊩⋆ ζ δ)
eval (unbox t u) γ δ = eval u γ (δ ∙ (eval t γ δ) reflR)
eval unit        γ δ = tt
eval (pair t u)  γ δ = eval t γ δ ∙ eval u γ δ
eval (fst t)     γ δ = proj₁ (eval t γ δ)
eval (snd t)     γ δ = proj₂ (eval t γ δ)


-- Equipment for the canonical model.

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


-- The canonical model.
-- NOTE: This is almost certainly wrong.

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


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (Γ ∙ Δ) ⊩ A
  reflect {ᴬ P}   t = t
  reflect {A ▷ B} t = λ { {Γ′ ∙ Δ′} (η ∙ θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (Γ ∙ Δ) R² (Γ′ ∙ Δ′) → (Γ′ ∙ Δ′) ⊩ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ bot⊆ (mmono⊢ θ t)) mv₀)
  reflect {⫪}    t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ A → Γ ⨾ Δ ⊢ A
  reify {ᴬ P}   s       = s
  reify {A ▷ B} f       = lam (reify {B} (f (weak⊆ ∙ refl⊆) (reflect {A} v₀)))
  reify {□ A}   f       = box (reify {A} (f {!jump ?!}))
  reify {⫪}    tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩⋆ : ∀ {Γ Δ} → (Γ ∙ Δ) ⊩⋆ Γ
refl⊩⋆ {⌀}     = tt
refl⊩⋆ {Γ , A} = mono⊩⋆ {Γ} (weak⊆ ∙ refl⊆) refl⊩⋆ ∙ reflect {A} v₀

mrefl⊩⋆ : ∀ {Δ Γ} → (Γ ∙ Δ) ⊩⋆ Δ
mrefl⊩⋆ {⌀}     = tt
mrefl⊩⋆ {Δ , A} = mmono⊩⋆ {Δ} (step refl⊆ weak⊆) mrefl⊩⋆ ∙ reflect {A} mv₀


-- Completeness, or quotation.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ᴹ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
