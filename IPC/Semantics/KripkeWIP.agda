module IPC.Semantics.KripkeWIP where

open import IPC.Gentzen public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  field
    World   : Set
    _≤_     : World → World → Set
    refl≤   : ∀ {w} → w ≤ w
    trans≤  : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    _⊩ₐ_   : World → Atom → Set
    mono⊩ₐ : ∀ {p w w′} → w ≤ w′ → w ⊩ₐ p → w′ ⊩ₐ p

open Model {{…}} public


-- Truth in a model.

module _ {{_ : Model}} where
  _⊩ₜ_ : World → Ty → Set
  w ⊩ₜ (α p)    = w ⊩ₐ p
  w ⊩ₜ (A ⇒ B) = ∀ {w′} → w ≤ w′ → w′ ⊩ₜ A → w′ ⊩ₜ B
  w ⊩ₜ ⊤       = Unit
  w ⊩ₜ (A ∧ B)  = w ⊩ₜ A × w ⊩ₜ B
  w ⊩ₜ (A ∨ B)  = w ⊩ₜ A + w ⊩ₜ B
  w ⊩ₜ ⊥       = Empty

  _⊩ᵢ_ : World → Cx Ty → Set
  w ⊩ᵢ ∅       = Unit
  w ⊩ᵢ (Γ , A) = w ⊩ᵢ Γ × w ⊩ₜ A


  -- Monotonicity of semantic consequence with respect to accessibility.

  mono⊩ₜ : ∀ {A w w′} → w ≤ w′ → w ⊩ₜ A → w′ ⊩ₜ A
  mono⊩ₜ {α p}    ξ s       = mono⊩ₐ ξ s
  mono⊩ₜ {A ⇒ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ₜ {⊤}     ξ τ       = τ
  mono⊩ₜ {A ∧ B}  ξ (a ∙ b) = mono⊩ₜ {A} ξ a ∙ mono⊩ₜ {B} ξ b
  mono⊩ₜ {A ∨ B}  ξ (ι₁ a)  = ι₁ (mono⊩ₜ {A} ξ a)
  mono⊩ₜ {A ∨ B}  ξ (ι₂ b)  = ι₂ (mono⊩ₜ {B} ξ b)
  mono⊩ₜ {⊥}     ξ ()

  mono⊩ᵢ : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᵢ Γ → w′ ⊩ᵢ Γ
  mono⊩ᵢ {∅}     ξ τ       = τ
  mono⊩ᵢ {Γ , A} ξ (γ ∙ a) = mono⊩ᵢ {Γ} ξ γ ∙ mono⊩ₜ {A} ξ a


-- Truth in all models.

_⊩_ : Cx Ty → Ty → Set₁
Γ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᵢ Γ → w ⊩ₜ A


-- Soundness with respect to all models.

lookup : ∀ {Γ A} → A ∈ Γ → Γ ⊩ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
eval (var i)      γ = lookup i γ
eval (lam t)      γ = λ ξ a → eval t (mono⊩ᵢ ξ γ ∙ a)
eval (app t u)    γ = (eval t γ) refl≤ (eval u γ)
eval unit         γ = τ
eval (pair t u)   γ = eval t γ ∙ eval u γ
eval (fst t)      γ with eval t γ
…                | a ∙ b = a
eval (snd t)      γ with eval t γ
…                | a ∙ b = b
eval (inl t)      γ = ι₁ (eval t γ)
eval (inr t)      γ = ι₂ (eval t γ)
eval (case t u v) γ with eval t γ
…                | ι₁ a = eval u (γ ∙ a)
…                | ι₂ b = eval v (γ ∙ b)
eval (boom t)     γ with eval t γ
…                | ()


-- Canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ₐ_   = λ Γ p → Γ ⊢ α p
    ; mono⊩ₐ = mono⊢
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ₜ A
  reflect {α p}    t = t
  reflect {A ⇒ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {⊤}     t = τ
  reflect {A ∧ B}  t = reflect {A} (fst t) ∙ reflect {B} (snd t)
  reflect {A ∨ B}  t = {!!}
  reflect {⊥}     t = {!!}

  reify : ∀ {A Γ} → Γ ⊩ₜ A → Γ ⊢ A
  reify {α p}    s       = s
  reify {A ⇒ B} f       = lam (reify {B} (f weak⊆ (reflect {A} v₀)))
  reify {⊤}     τ       = unit
  reify {A ∧ B}  (a ∙ b) = pair (reify {A} a) (reify {B} b)
  reify {A ∨ B}  (ι₁ a)  = inl (reify {A} a)
  reify {A ∨ B}  (ι₂ b)  = inr (reify {B} b)
  reify {⊥}     ()

refl⊩ᵢ : ∀ {Γ} → Γ ⊩ᵢ Γ
refl⊩ᵢ {∅}     = τ
refl⊩ᵢ {Γ , A} = mono⊩ᵢ {Γ} weak⊆ refl⊩ᵢ ∙ reflect {A} v₀


-- Completeness with respect to all models.

quot : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩ᵢ)


-- Canonicity.

canon₁ : ∀ {A Γ} → Γ ⊩ₜ A → Γ ⊩ A
canon₁ {A} = eval ∘ reify {A}

canon₂ : ∀ {A Γ} → Γ ⊩ A → Γ ⊩ₜ A
canon₂ {A} = reflect {A} ∘ quot


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
