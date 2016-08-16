module BasicIPC.Metatheory.OpenGentzen-KripkeGodel where

open import BasicIPC.Syntax.OpenGentzen public
open import BasicIPC.Semantics.KripkeGodel public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app t u)  γ = (eval t γ refl≤) (eval u γ)
eval (pair t u) γ = λ ξ → let γ′ = mono⊩⋆ ξ γ in eval t γ′ , eval u γ′
eval (fst t)    γ = π₁ (eval t γ refl≤)
eval (snd t)    γ = π₂ (eval t γ refl≤)
eval tt         γ = λ ξ → ∙

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → ∀ᴹʷ⊩ Γ ⇒⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ

-- Alternative version.
eval′ : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval′ (var i)            γ = lookup i γ
eval′ (lam {A} {B} t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval′ (app {A} {B} t u)  γ = _⟪$⟫_ {A} {B} (eval′ t γ) (eval′ u γ)
eval′ (pair {A} {B} t u) γ = _⟪,⟫_ {A} {B} (eval′ t γ) refl≤ (eval′ u γ)
eval′ (fst {A} {B} t)    γ = ⟪π₁⟫ {A} {B} (eval′ t γ)
eval′ (snd {A} {B} t)    γ = ⟪π₂⟫ {A} {B} (eval′ t γ)
eval′ tt                 γ = const ∙

-- Alternative version.
eval″ : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval″ (var i)            γ = lookup i γ
eval″ (lam {A} {B} t)    γ = ⟦λ⟧ {A} {B} (eval″ t) γ
eval″ (app {A} {B} t u)  γ = _⟦$⟧_ {A} {B} (eval″ t) (eval″ u) γ
eval″ (pair {A} {B} t u) γ = _⟦,⟧_ {A} {B} (eval″ t) (eval″ u) γ
eval″ (fst {A} {B} t)    γ = ⟦π₁⟧ {A} {B} (eval″ t) γ
eval″ (snd {A} {B} t)    γ = ⟦π₂⟧ {A} {B} (eval″ t) γ
eval″ tt                 γ = const ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { World  = Cx Ty
    ; _≤_    = _⊆_
    ; refl≤  = refl⊆
    ; trans≤ = trans⊆
    ; _⊩ᵅ_  = λ Γ P → Γ ⊢ α P
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = λ η → mono⊢ η t
  reflect {A ▻ B} t = λ η a → reflect {B} (app (mono⊢ η t) (reify {A} a))
  reflect {A ∧ B} t = λ η → reflect {A} (fst (mono⊢ η t)) , reflect {B} (snd (mono⊢ η t))
  reflect {⊤}    t = λ η → ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s refl⊆
  reify {A ▻ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {A ∧ B} s = pair (reify {A} (π₁ (s refl⊆))) (reify {B} (π₂ (s refl⊆)))
  reify {⊤}    s = tt

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → ∀ᴹʷ⊩ Γ ⇒ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
