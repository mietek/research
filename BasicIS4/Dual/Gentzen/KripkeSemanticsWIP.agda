module BasicIS4.Dual.Gentzen.KripkeSemanticsWIP where

open import BasicIS4.Dual.Gentzen.Core public


-- Non-standard intuitionistic modal Kripke models, based on Marti and Studer.

record Model : Set₁ where
  infix 3 _≤_ _R_ _⊩ᵅ_
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
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {w w′ p} → w ≤ w′ → w ⊩ᵅ p → w′ ⊩ᵅ p

    -- Modal accessibility is ??? with respect to intuitionistic accessibility;
    -- seems odd, but appears in Ono; repeated by Marti and Studer.
    fnordR : ∀ {w w′ w″} → w ≤ w′ → w′ R w″ → w R w″

    -- NEW: Forcing is monotonic with respect to modal accessibility; needed for soundness;
    -- seems OK.
    mmono⊩ᵅ : ∀ {w w′ p} → w R w′ → w ⊩ᵅ p → w′ ⊩ᵅ p

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
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A   = ∀ {w′} → w R w′ → w′ ⊩ A
  w ⊩ A ∧ B = w ⊩ A ᴬ∧ w ⊩ B
  w ⊩ ⊤    = ᴬ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ s = λ ζ → s (fnordR ξ ζ)
  mono⊩ {A ∧ B} ξ s = ᴬpair (mono⊩ {A} ξ (ᴬfst s)) (mono⊩ {B} ξ (ᴬsnd s))
  mono⊩ {⊤}    ξ s = ᴬtt

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬpair (mono⊩⋆ {Γ} ξ (ᴬfst γ)) (mono⊩ {A} ξ (ᴬsnd γ))


  -- Monotonicity with respect to modal accessibility.

  mmono⊩ : ∀ {A w w′} → w R w′ → w ⊩ A → w′ ⊩ A
  mmono⊩ {α P}   ζ s = mmono⊩ᵅ ζ s
  mmono⊩ {A ▷ B} ζ s = λ ξ a → s (mfnord≤ ζ ξ) a
  mmono⊩ {□ A}   ζ s = λ ζ′ → s (transR ζ ζ′)
  mmono⊩ {A ∧ B} ζ s = ᴬpair (mmono⊩ {A} ζ (ᴬfst s)) (mmono⊩ {B} ζ (ᴬsnd s))
  mmono⊩ {⊤}    ζ s = ᴬtt

  mmono⊩⋆ : ∀ {Δ w w′} → w R w′ → w ⊩⋆ Δ → w′ ⊩⋆ Δ
  mmono⊩⋆ {⌀}     ζ δ = ᴬtt
  mmono⊩⋆ {Δ , A} ζ δ = ᴬpair (mmono⊩⋆ {Δ} ζ (ᴬfst δ)) (mmono⊩ {A} ζ (ᴬsnd δ))


-- Forcing in all models.

infix 3 _⨾_ᴹ⊩_
_⨾_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Δ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ᴹ⊩ A
lookup top     γ δ = ᴬsnd γ
lookup (pop i) γ δ = lookup i (ᴬfst γ) δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ᴹ⊩ A
mlookup top     γ δ = ᴬsnd δ
mlookup (pop i) γ δ = mlookup i γ (ᴬfst δ)

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ᴹ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (ᴬpair (mono⊩⋆ ξ γ) a) (mono⊩⋆ ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t ᴬtt (mmono⊩⋆ ζ δ)
eval (unbox t u) γ δ = (eval u γ) (ᴬpair δ ((eval t γ δ) reflR))
eval (pair t u)  γ δ = ᴬpair (eval t γ δ) (eval u γ δ)
eval (fst t)     γ δ = ᴬfst (eval t γ δ)
eval (snd t)     γ δ = ᴬsnd (eval t γ δ)
eval tt          γ δ = ᴬtt


-- Equipment for the canonical model.

Cx² : Set → Set
Cx² U = Cx U ᴬ∧ Cx U

module _ {U : Set} where
  infix 3 _⊆²_
  _⊆²_ : Cx² U → Cx² U → Set
  (ᴬpair Γ Δ) ⊆² (ᴬpair Γ′ Δ′) = (Γ ⊆ Γ′) ᴬ∧ (Δ ⊆ Δ′)

  refl⊆² : ∀ {Ξ} → Ξ ⊆² Ξ
  refl⊆² = ᴬpair refl⊆ refl⊆

  trans⊆² : ∀ {Ξ Ξ′ Ξ″} → Ξ ⊆² Ξ′ → Ξ′ ⊆² Ξ″ → Ξ ⊆² Ξ″
  trans⊆² (ᴬpair η θ) (ᴬpair η′ θ′) = ᴬpair (trans⊆ η η′) (trans⊆ θ θ′)

  infix 3 _R²_
  data _R²_ : Cx² U → Cx² U → Set where
    step : ∀ {Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → (ᴬpair Γ Δ) R² (ᴬpair Γ′ Δ′)
    jump : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → (ᴬpair ⌀ Δ) R² (ᴬpair Γ Δ′)

  ⊆²→R² : ∀ {Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ R² Ξ′
  ⊆²→R² (ᴬpair η θ) = step η θ

  R²→⊆² : ∀ {Ξ Ξ′} → Ξ R² Ξ′ → Ξ ⊆² Ξ′
  R²→⊆² (step η θ) = ᴬpair η θ
  R²→⊆² (jump θ)   = ᴬpair bot⊆ θ

  reflR² : ∀ {Ξ} → Ξ R² Ξ
  reflR² = step refl⊆ refl⊆

  transR² : ∀ {Ξ Ξ′ Ξ″} → Ξ R² Ξ′ → Ξ′ R² Ξ″ → Ξ R² Ξ″
  transR² (step η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  transR² (step η θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)
  transR² (jump θ)   (step η′ θ′) = jump (trans⊆ θ θ′)
  transR² (jump θ)   (jump θ′)    = jump (trans⊆ θ θ′)

  fnordR² : ∀ {X Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ′ R² X → Ξ R² X
  fnordR² (ᴬpair η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  fnordR² (ᴬpair η θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)

  mfnord⊆² : ∀ {X Ξ Ξ′} → Ξ R² Ξ′ → Ξ′ ⊆² X → Ξ ⊆² X
  mfnord⊆² (step η θ) (ᴬpair η′ θ′) = ᴬpair (trans⊆ η η′) (trans⊆ θ θ′)
  mfnord⊆² (jump θ)   (ᴬpair η′ θ′) = ᴬpair bot⊆ (trans⊆ θ θ′)

infix 3 _⊢²_
_⊢²_ : Cx² Ty → Ty → Set
(ᴬpair Γ Δ) ⊢² A = Γ ⨾ Δ ⊢ A

mono⊢² : ∀ {A Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ ⊢² A → Ξ′ ⊢² A
mono⊢² (ᴬpair η θ) = mono⊢ η ∘ mmono⊢ θ

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
    ; _⊩ᵅ_    = λ { Ξ P → Ξ ⊢² α P }
    ; mono⊩ᵅ  = mono⊢²
    ; fnordR   = fnordR²
    ; mmono⊩ᵅ = mmono⊢²
    ; mfnord≤  = mfnord⊆²
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (ᴬpair Γ Δ) ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ { {ᴬpair Γ′ Δ′} (ᴬpair η θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (ᴬpair Γ Δ) R² (ᴬpair Γ′ Δ′) → (ᴬpair Γ′ Δ′) ⊩ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ bot⊆ (mmono⊢ θ t)) mv₀)
  reflect {A ∧ B} t = ᴬpair (reflect {A} (fst t)) (reflect {B} (snd t))
  reflect {⊤}    t = ᴬtt

  reify : ∀ {A Γ Δ} → (ᴬpair Γ Δ) ⊩ A → Γ ⨾ Δ ⊢ A
  reify {α P}   s = s
  reify {A ▷ B} s = lam (reify {B} (s (ᴬpair weak⊆ refl⊆) (reflect {A} v₀)))
  reify {□ A}   s = box (reify {A} (s {!jump ?!}))
  reify {A ∧ B} s = pair (reify {A} (ᴬfst s)) (reify {B} (ᴬsnd s))
  reify {⊤}    s = tt

refl⊩⋆ : ∀ {Γ Δ} → (ᴬpair Γ Δ) ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬtt
refl⊩⋆ {Γ , A} = ᴬpair (mono⊩⋆ {Γ} (ᴬpair weak⊆ refl⊆) refl⊩⋆) (reflect {A} v₀)

mrefl⊩⋆ : ∀ {Δ Γ} → (ᴬpair Γ Δ) ⊩⋆ Δ
mrefl⊩⋆ {⌀}     = ᴬtt
mrefl⊩⋆ {Δ , A} = ᴬpair (mmono⊩⋆ {Δ} (step refl⊆ weak⊆) mrefl⊩⋆) (reflect {A} mv₀)


-- Completeness, or quotation.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ᴹ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
