module BasicIS4.DualContext.Gentzen.KripkeSemanticsWIP where

open import BasicIS4.DualContext.Gentzen.Core public


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
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

    -- Modal accessibility is ??? with respect to intuitionistic accessibility;
    -- seems odd, but appears in Ono; repeated by Marti and Studer.
    fnordR : ∀ {x w w′} → w ≤ w′ → w′ R x → w R x

    -- NEW: Forcing is monotonic with respect to modal accessibility; needed for soundness;
    -- seems OK.
    mmono⊩ᵅ : ∀ {P w w′} → w R w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

    -- NEW: Intuitionistic accessibility is ??? with respect to modal accessibility;
    -- needed for soundness; seems odd.
    mfnord≤ : ∀ {x w w′} → w R w′ → w′ ≤ x → w ≤ x

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
  w ⊩ A ∧ B = w ⊩ A ᴬᵍ∧ w ⊩ B
  w ⊩ ⊤    = ᴬᵍ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬᵍ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬᵍ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ s = λ ζ → s (fnordR ξ ζ)
  mono⊩ {A ∧ B} ξ s = ᴬᵍpair (mono⊩ {A} ξ (ᴬᵍfst s)) (mono⊩ {B} ξ (ᴬᵍsnd s))
  mono⊩ {⊤}    ξ s = ᴬᵍtt

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬᵍtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬᵍpair (mono⊩⋆ {Γ} ξ (ᴬᵍfst γ)) (mono⊩ {A} ξ (ᴬᵍsnd γ))


  -- Monotonicity with respect to modal accessibility.

  mmono⊩ : ∀ {A w w′} → w R w′ → w ⊩ A → w′ ⊩ A
  mmono⊩ {α P}   ζ s = mmono⊩ᵅ ζ s
  mmono⊩ {A ▷ B} ζ s = λ ξ a → s (mfnord≤ ζ ξ) a
  mmono⊩ {□ A}   ζ s = λ ζ′ → s (transR ζ ζ′)
  mmono⊩ {A ∧ B} ζ s = ᴬᵍpair (mmono⊩ {A} ζ (ᴬᵍfst s)) (mmono⊩ {B} ζ (ᴬᵍsnd s))
  mmono⊩ {⊤}    ζ s = ᴬᵍtt

  mmono⊩⋆ : ∀ {Δ w w′} → w R w′ → w ⊩⋆ Δ → w′ ⊩⋆ Δ
  mmono⊩⋆ {⌀}     ζ δ = ᴬᵍtt
  mmono⊩⋆ {Δ , A} ζ δ = ᴬᵍpair (mmono⊩⋆ {Δ} ζ (ᴬᵍfst δ)) (mmono⊩ {A} ζ (ᴬᵍsnd δ))


-- Forcing in all models.

infix 3 _⨾_ᴹ⊩_
_⨾_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Δ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ᴹ⊩ A
lookup top     γ δ = ᴬᵍsnd γ
lookup (pop i) γ δ = lookup i (ᴬᵍfst γ) δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ᴹ⊩ A
mlookup top     γ δ = ᴬᵍsnd δ
mlookup (pop i) γ δ = mlookup i γ (ᴬᵍfst δ)

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ᴹ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a) (mono⊩⋆ ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t ᴬᵍtt (mmono⊩⋆ ζ δ)
eval (unbox t u) γ δ = (eval u γ) (ᴬᵍpair δ ((eval t γ δ) reflR))
eval (pair t u)  γ δ = ᴬᵍpair (eval t γ δ) (eval u γ δ)
eval (fst t)     γ δ = ᴬᵍfst (eval t γ δ)
eval (snd t)     γ δ = ᴬᵍsnd (eval t γ δ)
eval tt          γ δ = ᴬᵍtt


-- Equipment for the canonical model.

Cx² : Set → Set
Cx² U = Cx U ᴬᵍ∧ Cx U

module _ {U : Set} where
  infix 3 _⊆²_
  _⊆²_ : Cx² U → Cx² U → Set
  (ᴬᵍpair Γ Δ) ⊆² (ᴬᵍpair Γ′ Δ′) = (Γ ⊆ Γ′) ᴬᵍ∧ (Δ ⊆ Δ′)

  refl⊆² : ∀ {Ξ} → Ξ ⊆² Ξ
  refl⊆² = ᴬᵍpair refl⊆ refl⊆

  trans⊆² : ∀ {Ξ Ξ′ Ξ″} → Ξ ⊆² Ξ′ → Ξ′ ⊆² Ξ″ → Ξ ⊆² Ξ″
  trans⊆² (ᴬᵍpair η θ) (ᴬᵍpair η′ θ′) = ᴬᵍpair (trans⊆ η η′) (trans⊆ θ θ′)

  infix 3 _R²_
  data _R²_ : Cx² U → Cx² U → Set where
    step : ∀ {Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → (ᴬᵍpair Γ Δ) R² (ᴬᵍpair Γ′ Δ′)
    jump : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → (ᴬᵍpair ⌀ Δ) R² (ᴬᵍpair Γ Δ′)

  ⊆²→R² : ∀ {Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ R² Ξ′
  ⊆²→R² (ᴬᵍpair η θ) = step η θ

  R²→⊆² : ∀ {Ξ Ξ′} → Ξ R² Ξ′ → Ξ ⊆² Ξ′
  R²→⊆² (step η θ) = ᴬᵍpair η θ
  R²→⊆² (jump θ)   = ᴬᵍpair bot⊆ θ

  reflR² : ∀ {Ξ} → Ξ R² Ξ
  reflR² = step refl⊆ refl⊆

  transR² : ∀ {Ξ Ξ′ Ξ″} → Ξ R² Ξ′ → Ξ′ R² Ξ″ → Ξ R² Ξ″
  transR² (step η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  transR² (step η θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)
  transR² (jump θ)   (step η′ θ′) = jump (trans⊆ θ θ′)
  transR² (jump θ)   (jump θ′)    = jump (trans⊆ θ θ′)

  fnordR² : ∀ {X Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ′ R² X → Ξ R² X
  fnordR² (ᴬᵍpair η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  fnordR² (ᴬᵍpair η θ) (jump θ′)    = step (trans⊆ η bot⊆) (trans⊆ θ θ′)

  mfnord⊆² : ∀ {X Ξ Ξ′} → Ξ R² Ξ′ → Ξ′ ⊆² X → Ξ ⊆² X
  mfnord⊆² (step η θ) (ᴬᵍpair η′ θ′) = ᴬᵍpair (trans⊆ η η′) (trans⊆ θ θ′)
  mfnord⊆² (jump θ)   (ᴬᵍpair η′ θ′) = ᴬᵍpair bot⊆ (trans⊆ θ θ′)

infix 3 _⊢²_
_⊢²_ : Cx² Ty → Ty → Set
(ᴬᵍpair Γ Δ) ⊢² A = Γ ⨾ Δ ⊢ A

mono⊢² : ∀ {A Ξ Ξ′} → Ξ ⊆² Ξ′ → Ξ ⊢² A → Ξ′ ⊢² A
mono⊢² (ᴬᵍpair η θ) = mono⊢ η ∘ mmono⊢ θ

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
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (ᴬᵍpair Γ Δ) ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ { {ᴬᵍpair Γ′ Δ′} (ᴬᵍpair η θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (ᴬᵍpair Γ Δ) R² (ᴬᵍpair Γ′ Δ′) → (ᴬᵍpair Γ′ Δ′) ⊩ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ bot⊆ (mmono⊢ θ t)) mv₀)
  reflect {A ∧ B} t = ᴬᵍpair (reflect {A} (fst t)) (reflect {B} (snd t))
  reflect {⊤}    t = ᴬᵍtt

  reify : ∀ {A Γ Δ} → (ᴬᵍpair Γ Δ) ⊩ A → Γ ⨾ Δ ⊢ A
  reify {α P}   s = s
  reify {A ▷ B} s = lam (reify {B} (s (ᴬᵍpair weak⊆ refl⊆) (reflect {A} v₀)))
  reify {□ A}   s = box (reify {A} (s {!jump ?!}))
  reify {A ∧ B} s = pair (reify {A} (ᴬᵍfst s)) (reify {B} (ᴬᵍsnd s))
  reify {⊤}    s = tt

refl⊩⋆ : ∀ {Γ Δ} → (ᴬᵍpair Γ Δ) ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬᵍtt
refl⊩⋆ {Γ , A} = ᴬᵍpair (mono⊩⋆ {Γ} (ᴬᵍpair weak⊆ refl⊆) refl⊩⋆) (reflect {A} v₀)

mrefl⊩⋆ : ∀ {Δ Γ} → (ᴬᵍpair Γ Δ) ⊩⋆ Δ
mrefl⊩⋆ {⌀}     = ᴬᵍtt
mrefl⊩⋆ {Δ , A} = ᴬᵍpair (mmono⊩⋆ {Δ} (step refl⊆ weak⊆) mrefl⊩⋆) (reflect {A} mv₀)


-- Completeness, or quotation.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ᴹ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
