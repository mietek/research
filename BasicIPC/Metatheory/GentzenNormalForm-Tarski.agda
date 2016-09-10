module BasicIPC.Metatheory.GentzenNormalForm-Tarski where

open import BasicIPC.Syntax.GentzenNormalForm public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (lam t)           γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval (pair t u)        γ = eval t γ , eval u γ
eval (fst t)           γ = π₁ (eval t γ)
eval (snd t)           γ = π₂ (eval t γ)
eval unit              γ = ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ = ∙
eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ w P → unwrap w ⊢ⁿᵉ α P
      ; mono⊩ᵅ = λ ξ t → mono⊢ⁿᵉ (unwrap≤ ξ) t
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A w} → unwrap w ⊢ⁿᵉ A → w ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ ξ a → reflectᶜ (appⁿᵉ (mono⊢ⁿᵉ (unwrap≤ ξ) t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A w} → w ⊩ A → unwrap w ⊢ⁿᶠ A
  reifyᶜ {α P}   s = neⁿᶠ s
  reifyᶜ {A ▻ B} s = lamⁿᶠ (reifyᶜ (s weak≤ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {A ∧ B} s = pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unitⁿᶠ

reflectᶜ⋆ : ∀ {Ξ w} → unwrap w ⊢⋆ⁿᵉ Ξ → w ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → unwrap w ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {w} → w ⊩⋆ unwrap w
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

trans⊩⋆ : ∀ {w w′ w″} → w ⊩⋆ unwrap w′ → w′ ⊩⋆ unwrap w″ → w ⊩⋆ unwrap w″
trans⊩⋆ ts us = eval⋆ (trans⊢⋆ (nf→tm⋆ (reifyᶜ⋆ ts)) (nf→tm⋆ (reifyᶜ⋆ us))) refl⊩⋆


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = nf→tm (reifyᶜ (s refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
