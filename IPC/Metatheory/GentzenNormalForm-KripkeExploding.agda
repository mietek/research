module IPC.Metatheory.GentzenNormalForm-KripkeExploding where

open import IPC.Syntax.GentzenNormalForm public
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

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ = ∙
eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


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
      ; _⊪ᵅ_   = λ Γ P → Γ ⊢ⁿᵉ α P
      ; mono⊪ᵅ = mono⊢ⁿᵉ
      ; _‼_     = λ Γ A → Γ ⊢ⁿᶠ A
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflectᶜ {α P}   t = return {α P} t
  reflectᶜ {A ▻ B} t = return {A ▻ B} λ η a →
                         reflectᶜ {B} (appⁿᵉ (mono⊢ⁿᵉ η t) (reifyᶜ {A} a))
  reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ {A} (fstⁿᵉ t) , reflectᶜ {B} (sndⁿᵉ t))
  reflectᶜ {⊤}    t = return {⊤} ∙
  reflectᶜ {⊥}    t = λ η k → neⁿᶠ (boomⁿᵉ (mono⊢ⁿᵉ η t))
  reflectᶜ {A ∨ B} t = λ η k → neⁿᶠ (caseⁿᵉ (mono⊢ⁿᵉ η t)
                                       (k weak⊆ (ι₁ (reflectᶜ {A} (varⁿᵉ top))))
                                       (k weak⊆ (ι₂ (reflectᶜ {B} (varⁿᵉ top)))))

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reifyᶜ {α P}   k = k refl≤ λ η s → neⁿᶠ s
  reifyᶜ {A ▻ B} k = k refl≤ λ η s → lamⁿᶠ (reifyᶜ {B} (s weak⊆ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {A ∧ B} k = k refl≤ λ η s → pairⁿᶠ (reifyᶜ {A} (π₁ s)) (reifyᶜ {B} (π₂ s))
  reifyᶜ {⊤}    k = k refl≤ λ η s → unitⁿᶠ
  reifyᶜ {⊥}    k = k refl≤ λ η ()
  reifyᶜ {A ∨ B} k = k refl≤ λ η s → elim⊎ s
                                        (λ a → inlⁿᶠ (reifyᶜ {A} (λ η′ k′ → a η′ k′)))
                                        (λ b → inrⁿᶠ (reifyᶜ {B} (λ η′ k′ → b η′ k′)))

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ⁿᵉ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = eval⋆ (trans⊢⋆ (nf→tm⋆ (reifyᶜ⋆ ts)) (nf→tm⋆ (reifyᶜ⋆ us))) refl⊩⋆


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = nf→tm (reifyᶜ (s refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
