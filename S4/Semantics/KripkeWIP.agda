module S4.Semantics.KripkeWIP where

open import S4.Gentzen.PfenningDavies public


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
    _⊩ᵃ_   : World → Atom → Set
    mono⊩ᵃ : ∀ {w w′ p} → w ≤ w′ → w ⊩ᵃ p → w′ ⊩ᵃ p

    -- Modal accessibility is ??? with respect to intuitionistic accessibility;
    -- seems odd, but appears in Ono; repeated by Marti and Studer.
    fnordR : ∀ {w w′ w″} → w ≤ w′ → w′ R w″ → w R w″

    -- NEW: Forcing is monotonic with respect to modal accessibility; needed for soundness proof;
    -- seems OK.
    mmono⊩ᵃ : ∀ {w w′ p} → w R w′ → w ⊩ᵃ p → w′ ⊩ᵃ p

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
  _⊩ᵗ_ : World → Ty → Set
  w ⊩ᵗ (α p)   = w ⊩ᵃ p
  w ⊩ᵗ (A ⊃ B) = ∀ {w′} → w ≤ w′ → w′ ⊩ᵗ A → w′ ⊩ᵗ B
  w ⊩ᵗ (□ A)   = ∀ {w′} → w R w′ → w′ ⊩ᵗ A
  w ⊩ᵗ ι       = ⊤
  w ⊩ᵗ (A ∧ B) = w ⊩ᵗ A × w ⊩ᵗ B

  _⊩ᶜ_ : World → Cx Ty → Set
  w ⊩ᶜ ⌀       = ⊤
  w ⊩ᶜ (Γ , A) = w ⊩ᶜ Γ × w ⊩ᵗ A


  -- Monotonicity of semantic consequence with respect to intuitionistic accessibility.

  mono⊩ᵗ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵗ A → w′ ⊩ᵗ A
  mono⊩ᵗ {α p}   ξ s       = mono⊩ᵃ ξ s
  mono⊩ᵗ {A ⊃ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵗ {□ A}   ξ f       = λ ζ → f (fnordR ξ ζ)
  mono⊩ᵗ {ι}     ξ tt      = tt
  mono⊩ᵗ {A ∧ B} ξ (a ∙ b) = mono⊩ᵗ {A} ξ a ∙ mono⊩ᵗ {B} ξ b

  mono⊩ᶜ : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᶜ Γ → w′ ⊩ᶜ Γ
  mono⊩ᶜ {⌀}     ξ tt      = tt
  mono⊩ᶜ {Γ , A} ξ (γ ∙ a) = mono⊩ᶜ {Γ} ξ γ ∙ mono⊩ᵗ {A} ξ a


  -- Monotonicity of semantic consequence with respect to modal accessibility.

  mmono⊩ᵗ : ∀ {A w w′} → w R w′ → w ⊩ᵗ A → w′ ⊩ᵗ A
  mmono⊩ᵗ {α p}   ζ s       = mmono⊩ᵃ ζ s
  mmono⊩ᵗ {A ⊃ B} ζ f       = λ ξ a → f (mfnord≤ ζ ξ) a
  mmono⊩ᵗ {□ A}   ζ f       = λ ζ′ → f (transR ζ ζ′)
  mmono⊩ᵗ {ι}     ζ tt      = tt
  mmono⊩ᵗ {A ∧ B} ζ (a ∙ b) = mmono⊩ᵗ {A} ζ a ∙ mmono⊩ᵗ {B} ζ b

  mmono⊩ᶜ : ∀ {Δ w w′} → w R w′ → w ⊩ᶜ Δ → w′ ⊩ᶜ Δ
  mmono⊩ᶜ {⌀}     ζ tt      = tt
  mmono⊩ᶜ {Δ , A} ζ (δ ∙ a) = mmono⊩ᶜ {Δ} ζ δ ∙ mmono⊩ᵗ {A} ζ a


-- Truth in all models.

_⨾_⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⨾ Δ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᶜ Γ → w ⊩ᶜ Δ → w ⊩ᵗ A


-- Soundness with respect to all models.

lookup : ∀ {A Γ Δ} → A ∈ Γ → Γ ⨾ Δ ⊩ A
lookup top     (γ ∙ a) δ = a
lookup (pop i) (γ ∙ b) δ = lookup i γ δ

mlookup : ∀ {A Γ Δ} → A ∈ Δ → Γ ⨾ Δ ⊩ A
mlookup top     γ (δ ∙ a) = a
mlookup (pop i) γ (δ ∙ b) = mlookup i γ δ

eval : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊩ A
eval (var i)     γ δ = lookup i γ δ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩ᶜ ξ γ ∙ a) (mono⊩ᶜ ξ δ)
eval (app t u)   γ δ = (eval t γ δ) refl≤ (eval u γ δ)
eval (mvar i)    γ δ = mlookup i γ δ
eval (box t)     γ δ = λ ζ → eval t tt (mmono⊩ᶜ ζ δ)
eval (unbox t u) γ δ = eval u γ (δ ∙ (eval t γ δ) reflR)
eval unit        γ δ = tt
eval (pair t u)  γ δ = eval t γ δ ∙ eval u γ δ
eval (fst t)     γ δ with eval t γ δ
…                   | a ∙ b = a
eval (snd t)     γ δ with eval t γ δ
…                   | a ∙ b = b


-- Canonical model.

Cx₂ : Set → Set
Cx₂ U = Cx U × Cx U

module _ {U : Set} where
  infix 1 _⊆₂_
  _⊆₂_ : Cx₂ U → Cx₂ U → Set
  (Γ ∙ Δ) ⊆₂ (Γ′ ∙ Δ′) = (Γ ⊆ Γ′) × (Δ ⊆ Δ′)

  refl⊆₂ : ∀ {Ξ} → Ξ ⊆₂ Ξ
  refl⊆₂ = refl⊆ ∙ refl⊆

  trans⊆₂ : ∀ {Ξ Ξ′ Ξ″} → Ξ ⊆₂ Ξ′ → Ξ′ ⊆₂ Ξ″ → Ξ ⊆₂ Ξ″
  trans⊆₂ (η ∙ θ) (η′ ∙ θ′) = trans⊆ η η′ ∙ trans⊆ θ θ′

  infix 1 _R₂_
  data _R₂_ : Cx₂ U → Cx₂ U → Set where
    step : ∀ {Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → (Γ ∙ Δ) R₂ (Γ′ ∙ Δ′)
    jump : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → (⌀ ∙ Δ) R₂ (Γ ∙ Δ′)

  ⊆₂→R₂ : ∀ {Ξ Ξ′} → Ξ ⊆₂ Ξ′ → Ξ R₂ Ξ′
  ⊆₂→R₂ (η ∙ θ) = step η θ

  R₂→⊆₂ : ∀ {Ξ Ξ′} → Ξ R₂ Ξ′ → Ξ ⊆₂ Ξ′
  R₂→⊆₂ (step η θ) = η ∙ θ
  R₂→⊆₂ (jump θ)   = zero⊆ ∙ θ

  reflR₂ : ∀ {Ξ} → Ξ R₂ Ξ
  reflR₂ = step refl⊆ refl⊆

  transR₂ : ∀ {Ξ Ξ′ Ξ″} → Ξ R₂ Ξ′ → Ξ′ R₂ Ξ″ → Ξ R₂ Ξ″
  transR₂ (step η θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  transR₂ (step η θ) (jump θ′)    = step (trans⊆ η zero⊆) (trans⊆ θ θ′)
  transR₂ (jump θ)   (step η′ θ′) = jump (trans⊆ θ θ′)
  transR₂ (jump θ)   (jump θ′)    = jump (trans⊆ θ θ′)

  fnordR₂ : ∀ {X Ξ Ξ′} → Ξ ⊆₂ Ξ′ → Ξ′ R₂ X → Ξ R₂ X
  fnordR₂ (η ∙ θ) (step η′ θ′) = step (trans⊆ η η′) (trans⊆ θ θ′)
  fnordR₂ (η ∙ θ) (jump θ′)    = step (trans⊆ η zero⊆) (trans⊆ θ θ′)

  mfnord⊆₂ : ∀ {X Ξ Ξ′} → Ξ R₂ Ξ′ → Ξ′ ⊆₂ X → Ξ ⊆₂ X
  mfnord⊆₂ (step η θ) (η′ ∙ θ′) = trans⊆ η η′ ∙ trans⊆ θ θ′
  mfnord⊆₂ (jump θ)   (η′ ∙ θ′) = zero⊆ ∙ trans⊆ θ θ′

infix 0 _⊢₂_
_⊢₂_ : Cx₂ Ty → Ty → Set
(Γ ∙ Δ) ⊢₂ A = Γ ⨾ Δ ⊢ A

mono⊢₂ : ∀ {A Ξ Ξ′} → Ξ ⊆₂ Ξ′ → Ξ ⊢₂ A → Ξ′ ⊢₂ A
mono⊢₂ (η ∙ θ) = mono⊢ η ∘ mmono⊢ θ

mmono⊢₂ : ∀ {A Ξ Ξ′} → Ξ R₂ Ξ′ → Ξ ⊢₂ A → Ξ′ ⊢₂ A
mmono⊢₂ (step η θ) = mono⊢ η ∘ mmono⊢ θ
mmono⊢₂ (jump θ)   = mono⊢ zero⊆ ∘ mmono⊢ θ

instance
  canon : Model
  canon = record
    { World     = Cx₂ Ty
    ; _≤_       = _⊆₂_
    ; refl≤     = refl⊆₂
    ; trans≤    = trans⊆₂
    ; _R_       = _R₂_
    ; reflR     = reflR₂
    ; transR    = transR₂
    ; _⊩ᵃ_     = λ { Ξ p → Ξ ⊢₂ α p }
    ; mono⊩ᵃ   = mono⊢₂
    ; fnordR    = fnordR₂
    ; mmono⊩ᵃ  = mmono⊢₂
    ; mfnord≤   = mfnord⊆₂
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → (Γ ∙ Δ) ⊩ᵗ A
  reflect {α p}   t = t
  reflect {A ⊃ B} t = λ { {Γ′ ∙ Δ′} (η ∙ θ) a → reflect {B} (app (mono⊢ η (mmono⊢ θ t)) (reify {A} a)) }
  reflect {□ A}   t = aux t
    where aux : ∀ {Γ Γ′ Δ Δ′} → Γ ⨾ Δ ⊢ □ A → (Γ ∙ Δ) R₂ (Γ′ ∙ Δ′) → (Γ′ ∙ Δ′) ⊩ᵗ A
          aux t (step η θ) = reflect {A} (unbox (mono⊢ η (mmono⊢ θ t)) mv₀)
          aux t (jump θ)   = reflect {A} (unbox (mono⊢ zero⊆ (mmono⊢ θ t)) mv₀)
  reflect {ι}     t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ᵗ A → Γ ⨾ Δ ⊢ A
  reify {α p}   s       = s
  reify {A ⊃ B} f       = lam (reify {B} (f (weak⊆ ∙ refl⊆) (reflect {A} v₀)))
  reify {□ A}   f       = box (reify {A} (f {!jump ?!}))
  reify {ι}     tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᶜ : ∀ {Γ Δ} → (Γ ∙ Δ) ⊩ᶜ Γ
refl⊩ᶜ {⌀}     = tt
refl⊩ᶜ {Γ , A} = mono⊩ᶜ {Γ} (weak⊆ ∙ refl⊆) refl⊩ᶜ ∙ reflect {A} v₀

mrefl⊩ᶜ : ∀ {Δ Γ} → (Γ ∙ Δ) ⊩ᶜ Δ
mrefl⊩ᶜ {⌀}     = tt
mrefl⊩ᶜ {Δ , A} = mmono⊩ᶜ {Δ} (step refl⊆ weak⊆) mrefl⊩ᶜ ∙ reflect {A} mv₀


-- Completeness with respect to all models.

quot : ∀ {A Γ Δ} → Γ ⨾ Δ ⊩ A → Γ ⨾ Δ ⊢ A
quot t = reify (t refl⊩ᶜ mrefl⊩ᶜ)


-- Canonicity.

canon₁ : ∀ {A Γ Δ} → (Γ ∙ Δ) ⊩ᵗ A → Γ ⨾ Δ ⊩ A
canon₁ {A} = eval ∘ reify {A}

canon₂ : ∀ {A Γ Δ} → Γ ⨾ Δ ⊩ A → (Γ ∙ Δ) ⊩ᵗ A
canon₂ {A} = reflect {A} ∘ quot


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⨾ Δ ⊢ A → Γ ⨾ Δ ⊢ A
norm = quot ∘ eval
