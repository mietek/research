module IPC.Metatheory.Gentzen-KripkeExploding where

open import IPC.Syntax.Gentzen public
open import IPC.Semantics.KripkeExploding public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)                  γ = lookup i γ
eval (lam {A} {B} t)          γ = return {A ▻ B} λ ξ a →
                                    eval t (mono⊩⋆ ξ γ , a)
eval (app {A} {B} t u)        γ = bind {A ▻ B} {B} (eval t γ) λ ξ f →
                                    _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ ξ γ))
eval (pair {A} {B} t u)       γ = return {A ∧ B} (eval t γ , eval u γ)
eval (fst {A} {B} t)          γ = bind {A ∧ B} {A} (eval t γ) (K π₁)
eval (snd {A} {B} t)          γ = bind {A ∧ B} {B} (eval t γ) (K π₂)
eval unit                     γ = return {⊤} ∙
eval (boom {C} t)             γ = bind {⊥} {C} (eval t γ) (K elim𝟘)
eval (inl {A} {B} t)          γ = return {A ∨ B} (ι₁ (eval t γ))
eval (inr {A} {B} t)          γ = return {A ∨ B} (ι₂ (eval t γ))
eval (case {A} {B} {C} t u v) γ = bind {A ∨ B} {C} (eval t γ) λ ξ s → elim⊎ s
                                    (λ a → eval u (mono⊩⋆ ξ γ , λ ξ′ k → a ξ′ k))
                                    (λ b → eval v (mono⊩⋆ ξ γ , λ ξ′ k → b ξ′ k))


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { World   = Cx Ty
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      ; _⊪ᵅ_   = λ Γ P → Γ ⊢ α P
      ; mono⊪ᵅ = mono⊢
      ; _‼_     = λ Γ A → Γ ⊢ A
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = return {α P} t
  reflectᶜ {A ▻ B} t = return {A ▻ B} λ η a →
                         reflectᶜ {B} (app (mono⊢ η t) (reifyᶜ {A} a))
  reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ {A} (fst t) , reflectᶜ {B} (snd t))
  reflectᶜ {⊤}    t = return {⊤} ∙
  reflectᶜ {⊥}    t = λ η k → boom (mono⊢ η t)
  reflectᶜ {A ∨ B} t = λ η k → case (mono⊢ η t)
                                  (k weak⊆ (ι₁ (reflectᶜ {A} v₀)))
                                  (k weak⊆ (ι₂ (reflectᶜ {B} (v₀))))

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   k = k refl≤ λ η s → s
  reifyᶜ {A ▻ B} k = k refl≤ λ η s → lam (reifyᶜ {B} (s weak⊆ (reflectᶜ {A} (v₀))))
  reifyᶜ {A ∧ B} k = k refl≤ λ η s → pair (reifyᶜ {A} (π₁ s)) (reifyᶜ {B} (π₂ s))
  reifyᶜ {⊤}    k = k refl≤ λ η s → unit
  reifyᶜ {⊥}    k = k refl≤ λ η ()
  reifyᶜ {A ∨ B} k = k refl≤ λ η s → elim⊎ s
                                        (λ a → inl (reifyᶜ {A} (λ η′ k → a η′ k)))
                                        (λ b → inr (reifyᶜ {B} (λ η′ k → b η′ k)))

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
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
