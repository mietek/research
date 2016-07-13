module IS4.Dual.Semantics.KripkeWIP where

open import IS4.Dual.Gentzen public


-- Non-standard intuitionistic modal Kripke models, based on Marti and Studer.

record Model : Set₁ where
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


-- Truth in a model.

module _ {{_ : Model}} where
  _⊩ᵀ_ : World → Ty → Set
  w ⊩ᵀ (α p)   = w ⊩ᴬ p
  w ⊩ᵀ (A ⊃ B) = ∀ {w′} → w ≤ w′ → w′ ⊩ᵀ A → w′ ⊩ᵀ B
  w ⊩ᵀ (□ A)   = ∀ {w′} → w R w′ → w′ ⊩ᵀ A
  w ⊩ᵀ ι       = ⊤
  w ⊩ᵀ (A ∧ B) = w ⊩ᵀ A × w ⊩ᵀ B

  _⊩ᵀ*_ : World → Cx Ty → Set
  w ⊩ᵀ* ⌀       = ⊤
  w ⊩ᵀ* (Γ , A) = w ⊩ᵀ* Γ × w ⊩ᵀ A


  -- Monotonicity of semantic consequence with respect to intuitionistic accessibility.

  mono⊩ᵀ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mono⊩ᵀ {α p}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ᵀ {A ⊃ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵀ {□ A}   ξ f       = λ ζ → f (fnordR ξ ζ)
  mono⊩ᵀ {ι}     ξ tt      = tt
  mono⊩ᵀ {A ∧ B} ξ (a ∙ b) = mono⊩ᵀ {A} ξ a ∙ mono⊩ᵀ {B} ξ b

  mono⊩ᵀ* : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᵀ* Γ → w′ ⊩ᵀ* Γ
  mono⊩ᵀ* {⌀}     ξ tt      = tt
  mono⊩ᵀ* {Γ , A} ξ (γ ∙ a) = mono⊩ᵀ* {Γ} ξ γ ∙ mono⊩ᵀ {A} ξ a


  -- Monotonicity of semantic consequence with respect to modal accessibility.

  mmono⊩ᵀ : ∀ {A w w′} → w R w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mmono⊩ᵀ {α p}   ζ s       = mmono⊩ᴬ ζ s
  mmono⊩ᵀ {A ⊃ B} ζ f       = λ ξ a → f (mfnord≤ ζ ξ) a
  mmono⊩ᵀ {□ A}   ζ f       = λ ζ′ → f (transR ζ ζ′)
  mmono⊩ᵀ {ι}     ζ tt      = tt
  mmono⊩ᵀ {A ∧ B} ζ (a ∙ b) = mmono⊩ᵀ {A} ζ a ∙ mmono⊩ᵀ {B} ζ b

  mmono⊩ᵀ* : ∀ {Δ w w′} → w R w′ → w ⊩ᵀ* Δ → w′ ⊩ᵀ* Δ
  mmono⊩ᵀ* {⌀}     ζ tt      = tt
  mmono⊩ᵀ* {Δ , A} ζ (δ ∙ a) = mmono⊩ᵀ* {Δ} ζ δ ∙ mmono⊩ᵀ {A} ζ a


-- Truth in all models.

_⨾_⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᵀ* Γ → w ⊩ᵀ* Δ → w ⊩ᵀ A


-- Soundness with respect to all models.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ⊩ A
lookup top     (γ ∙ a) δ = a
lookup (pop i) (γ ∙ b) δ = lookup i γ δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ⊩ A
mlookup top     γ (δ ∙ a) = a
mlookup (pop i) γ (δ ∙ b) = mlookup i γ δ

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩ᵀ* ξ γ ∙ a) (mono⊩ᵀ* ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t tt (mmono⊩ᵀ* ζ δ)
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
    ; _⊩ᴬ_    = λ { Ξ p → Ξ ⊢² α p }
    ; mono⊩ᴬ  = mono⊢²
    ; fnordR   = fnordR²
    ; mmono⊩ᴬ = mmono⊢²
    ; mfnord≤  = mfnord⊆²
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (Γ ∙ Δ) ⊩ᵀ A
  reflect {α p}   t = t
  reflect {A ⊃ B} t = λ { {Γ′ ∙ Δ′} (η ∙ θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (Γ ∙ Δ) R² (Γ′ ∙ Δ′) → (Γ′ ∙ Δ′) ⊩ᵀ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ bot⊆ (mmono⊢ θ t)) mv₀)
  reflect {ι}     t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ᵀ A → Γ ⨾ Δ ⊢ A
  reify {α p}   s       = s
  reify {A ⊃ B} f       = lam (reify {B} (f (weak⊆ ∙ refl⊆) (reflect {A} v₀)))
  reify {□ A}   f       = box (reify {A} (f {!jump ?!}))
  reify {ι}     tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᵀ* : ∀ {Γ Δ} → (Γ ∙ Δ) ⊩ᵀ* Γ
refl⊩ᵀ* {⌀}     = tt
refl⊩ᵀ* {Γ , A} = mono⊩ᵀ* {Γ} (weak⊆ ∙ refl⊆) refl⊩ᵀ* ∙ reflect {A} v₀

mrefl⊩ᵀ* : ∀ {Δ Γ} → (Γ ∙ Δ) ⊩ᵀ* Δ
mrefl⊩ᵀ* {⌀}     = tt
mrefl⊩ᵀ* {Δ , A} = mmono⊩ᵀ* {Δ} (step refl⊆ weak⊆) mrefl⊩ᵀ* ∙ reflect {A} mv₀


-- Completeness with respect to all models.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩ᵀ* mrefl⊩ᵀ*)


-- Canonicity.

canon₁ : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ᵀ A → Γ ⨾ Δ ⊩ A
canon₁ {A} = eval ∘ reify {A}

canon₂ : ∀ {A Γ Δ} → Γ ⨾ Δ ⊩ A → (Γ ∙ Δ) ⊩ᵀ A
canon₂ {A} = reflect {A} ∘ quot


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
