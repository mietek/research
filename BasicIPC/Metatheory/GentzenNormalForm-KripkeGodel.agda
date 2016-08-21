module BasicIPC.Metatheory.GentzenNormalForm-KripkeGodel where

open import BasicIPC.Syntax.GentzenNormalForm public
open import BasicIPC.Semantics.KripkeGodel public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)            γ = lookup i γ
eval (lam t)            γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app {A} {B} t u)  γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval (pair {A} {B} t u) γ = _⟪,⟫_ {A} {B} (eval t γ) (eval u γ)
eval (fst {A} {B} t)    γ = ⟪π₁⟫ {A} {B} (eval t γ)
eval (snd {A} {B} t)    γ = ⟪π₂⟫ {A} {B} (eval t γ)
eval tt                 γ = const ∙

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


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
      ; _⊩ᵅ_  = λ Γ P → Γ ⊢ⁿᵉ α P
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflectᶜ {α P}   t = λ η → mono⊢ⁿᵉ η t
  reflectᶜ {A ▻ B} t = λ η a → reflectᶜ (appⁿᵉ (mono⊢ⁿᵉ η t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = λ η → let t′ = mono⊢ⁿᵉ η t
                              in  reflectᶜ (fstⁿᵉ t′) , reflectᶜ (sndⁿᵉ t′)
  reflectᶜ {⊤}    t = λ η → ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reifyᶜ {α P}   s = neⁿᶠ (s refl⊆)
  reifyᶜ {A ▻ B} s = lamⁿᶠ (reifyᶜ (s weak⊆ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {A ∧ B} s = pairⁿᶠ (reifyᶜ (π₁ (s refl⊆))) (reifyᶜ (π₂ (s refl⊆)))
  reifyᶜ {⊤}    s = ttⁿᶠ

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᵉ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ⁿᶠ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊢⋆ⁿᵉ : ∀ {Γ} → Γ ⊢⋆ⁿᵉ Γ
refl⊢⋆ⁿᵉ {⌀}     = ∙
refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ weak⊆ refl⊢⋆ⁿᵉ , varⁿᵉ top

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
