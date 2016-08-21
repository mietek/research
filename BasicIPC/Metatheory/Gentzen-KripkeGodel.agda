module BasicIPC.Metatheory.Gentzen-KripkeGodel where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.KripkeGodel public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app t u)  γ = (eval t γ refl≤) (eval u γ)
eval (pair t u) γ = λ ξ → let γ′ = mono⊩⋆ ξ γ
                           in  eval t γ′ , eval u γ′
eval (fst t)    γ = π₁ (eval t γ refl≤)
eval (snd t)    γ = π₂ (eval t γ refl≤)
eval tt         γ = λ ξ → ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
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
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = λ η → mono⊢ η t
  reflectᶜ {A ▻ B} t = λ η a → reflectᶜ (app (mono⊢ η t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = λ η →
                        let t′ = mono⊢ η t
                        in  reflectᶜ (fst t′) , reflectᶜ (snd t′)
  reflectᶜ {⊤}    t = λ η → ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   s = s refl⊆
  reifyᶜ {A ▻ B} s = lam (reifyᶜ (s weak⊆ (reflectᶜ {A} v₀)))
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ (s refl⊆))) (reifyᶜ (π₂ (s refl⊆)))
  reifyᶜ {⊤}    s = tt

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


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
