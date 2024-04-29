module A201607.BasicIPC.Metatheory.Gentzen-KripkeConcrete where

open import A201607.BasicIPC.Syntax.Gentzen public
open import A201607.BasicIPC.Semantics.KripkeConcrete public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (lam t)           γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval (pair t u)        γ = eval t γ , eval u γ
eval (fst t)           γ = π₁ (eval t γ)
eval (snd t)           γ = π₂ (eval t γ)
eval unit              γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ w P → unwrap w ⊢ α P
      ; mono⊩ᵅ = λ ξ t → mono⊢ (unwrap≤ ξ) t
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A w} → unwrap w ⊢ A → w ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ ξ a → reflectᶜ (app (mono⊢ (unwrap≤ ξ) t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A w} → w ⊩ A → unwrap w ⊢ A
  reifyᶜ {α P}   s = s
  reifyᶜ {A ▻ B} s = lam (reifyᶜ (s weak≤ (reflectᶜ {A} v₀)))
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unit

reflectᶜ⋆ : ∀ {Ξ w} → unwrap w ⊢⋆ Ξ → w ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → unwrap w ⊢⋆ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {w} → w ⊩⋆ unwrap w
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {w w′ w″} → w ⊩⋆ unwrap w′ → w′ ⊩⋆ unwrap w″ → w ⊩⋆ unwrap w″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reifyᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
