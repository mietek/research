module BasicIPC.Metatheory.Gentzen-Tarski where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (lam t)           γ = λ η a → eval t (mono⊩⋆ η γ , a)
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval (pair t u)        γ = eval t γ , eval u γ
eval (fst t)           γ = π₁ (eval t γ)
eval (snd t)           γ = π₂ (eval t γ)
eval tt                γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ  = mono⊢
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ η a → reflectᶜ (app (mono⊢ η t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   s       = s
  reifyᶜ {A ▻ B} s       = lam (reifyᶜ (s weak⊆ (reflectᶜ {A} v₀)))
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reifyᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
