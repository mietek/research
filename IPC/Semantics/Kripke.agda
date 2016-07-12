module IPC.Semantics.Kripke where

open import IPC.Gentzen public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᴬ_   : World → Atom → Set
    mono⊩ᴬ : ∀ {p w w′} → w ≤ w′ → w ⊩ᴬ p → w′ ⊩ᴬ p

open Model {{…}} public


-- Truth in a model.

module _ {{_ : Model}} where
  _⊩ᵀ_ : World → Ty → Set
  w ⊩ᵀ (α p)   = w ⊩ᴬ p
  w ⊩ᵀ (A ⊃ B) = ∀ {w′} → w ≤ w′ → w′ ⊩ᵀ A → w′ ⊩ᵀ B
  w ⊩ᵀ ι       = ⊤
  w ⊩ᵀ (A ∧ B) = w ⊩ᵀ A × w ⊩ᵀ B

  _⊩ᵀ*_ : World → Cx Ty → Set
  w ⊩ᵀ* ⌀       = ⊤
  w ⊩ᵀ* (Γ , A) = w ⊩ᵀ* Γ × w ⊩ᵀ A


  -- Monotonicity of semantic consequence with respect to intuitionistic accessibility.

  mono⊩ᵀ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mono⊩ᵀ {α p}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ᵀ {A ⊃ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵀ {ι}     ξ tt      = tt
  mono⊩ᵀ {A ∧ B} ξ (a ∙ b) = mono⊩ᵀ {A} ξ a ∙ mono⊩ᵀ {B} ξ b

  mono⊩ᵀ* : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᵀ* Γ → w′ ⊩ᵀ* Γ
  mono⊩ᵀ* {⌀}     ξ tt      = tt
  mono⊩ᵀ* {Γ , A} ξ (γ ∙ a) = mono⊩ᵀ* {Γ} ξ γ ∙ mono⊩ᵀ {A} ξ a


-- Truth in all models.

_⊩_ : Cx Ty → Ty → Set₁
Γ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᵀ* Γ → w ⊩ᵀ A


-- Soundness with respect to all models.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ⊩ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩ᵀ* ξ γ ∙ a)
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
    ; _⊩ᴬ_   = λ Γ p → Γ ⊢ α p
    ; mono⊩ᴬ = mono⊢
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ᵀ A
  reflect {α p}   t = t
  reflect {A ⊃ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {ι}     t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ} → Γ ⊩ᵀ A → Γ ⊢ A
  reify {α p}   s       = s
  reify {A ⊃ B} f       = lam (reify {B} (f weak⊆ (reflect {A} v₀)))
  reify {ι}     tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᵀ* : ∀ {Γ} → Γ ⊩ᵀ* Γ
refl⊩ᵀ* {⌀}     = tt
refl⊩ᵀ* {Γ , A} = mono⊩ᵀ* {Γ} weak⊆ refl⊩ᵀ* ∙ reflect {A} v₀


-- Completeness with respect to all models.

quot : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩ᵀ*)


-- Canonicity.

canon₁ : ∀ {A Γ} → Γ ⊩ᵀ A → Γ ⊩ A
canon₁ {A} = eval ∘ reify {A}

canon₂ : ∀ {A Γ} → Γ ⊩ A → Γ ⊩ᵀ A
canon₂ {A} = reflect {A} ∘ quot


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
