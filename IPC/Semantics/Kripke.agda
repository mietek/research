module IPC.Semantics.Kripke where

open import IPC.Gentzen public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_     : World → World → Set
    refl≤   : ∀ {w} → w ≤ w
    trans≤  : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵃ_   : World → Atom → Set
    mono⊩ᵃ : ∀ {p w w′} → w ≤ w′ → w ⊩ᵃ p → w′ ⊩ᵃ p

open Model {{…}} public


-- Truth in a model.

module _ {{_ : Model}} where
  _⊩ᵗ_ : World → Ty → Set
  w ⊩ᵗ (α p)   = w ⊩ᵃ p
  w ⊩ᵗ (A ⊃ B) = ∀ {w′} → w ≤ w′ → w′ ⊩ᵗ A → w′ ⊩ᵗ B
  w ⊩ᵗ ι       = ⊤
  w ⊩ᵗ (A ∧ B) = w ⊩ᵗ A × w ⊩ᵗ B

  _⊩ᶜ_ : World → Cx Ty → Set
  w ⊩ᶜ ⌀       = ⊤
  w ⊩ᶜ (Γ , A) = w ⊩ᶜ Γ × w ⊩ᵗ A


  -- Monotonicity of semantic consequence with respect to intuitionistic accessibility.

  mono⊩ᵗ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵗ A → w′ ⊩ᵗ A
  mono⊩ᵗ {α p}   ξ s       = mono⊩ᵃ ξ s
  mono⊩ᵗ {A ⊃ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵗ {ι}     ξ tt      = tt
  mono⊩ᵗ {A ∧ B} ξ (a ∙ b) = mono⊩ᵗ {A} ξ a ∙ mono⊩ᵗ {B} ξ b

  mono⊩ᶜ : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᶜ Γ → w′ ⊩ᶜ Γ
  mono⊩ᶜ {⌀}     ξ tt      = tt
  mono⊩ᶜ {Γ , A} ξ (γ ∙ a) = mono⊩ᶜ {Γ} ξ γ ∙ mono⊩ᵗ {A} ξ a


-- Truth in all models.

_⊩_ : Cx Ty → Ty → Set₁
Γ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᶜ Γ → w ⊩ᵗ A


-- Soundness with respect to all models.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ⊩ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩ᶜ ξ γ ∙ a)
eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
eval unit       γ = tt
eval (pair t u) γ = eval t γ ∙ eval u γ
eval (fst t)    γ with eval t γ
…                | a ∙ b = a
eval (snd t)    γ with eval t γ
…                | a ∙ b = b


-- Canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᵃ_   = λ Γ p → Γ ⊢ α p
    ; mono⊩ᵃ = mono⊢
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ᵗ A
  reflect {α p}   t = t
  reflect {A ⊃ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {ι}     t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ} → Γ ⊩ᵗ A → Γ ⊢ A
  reify {α p}   s       = s
  reify {A ⊃ B} f       = lam (reify {B} (f weak⊆ (reflect {A} v₀)))
  reify {ι}     tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᶜ : ∀ {Γ} → Γ ⊩ᶜ Γ
refl⊩ᶜ {⌀}     = tt
refl⊩ᶜ {Γ , A} = mono⊩ᶜ {Γ} weak⊆ refl⊩ᶜ ∙ reflect {A} v₀


-- Completeness with respect to all models.

quot : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩ᶜ)


-- Canonicity.

canon₁ : ∀ {A Γ} → Γ ⊩ᵗ A → Γ ⊩ A
canon₁ {A} = eval ∘ reify {A}

canon₂ : ∀ {A Γ} → Γ ⊩ A → Γ ⊩ᵗ A
canon₂ {A} = reflect {A} ∘ quot


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
