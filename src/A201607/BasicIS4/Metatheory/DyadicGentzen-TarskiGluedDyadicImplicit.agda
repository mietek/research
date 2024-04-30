module A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicImplicit where

open import A201607.BasicIS4.Syntax.DyadicGentzen public
open import A201607.BasicIS4.Semantics.TarskiGluedDyadicImplicit public

open ImplicitSyntax (_⊢_) public


-- Soundness with respect to all models, or evaluation.

-- FIXME
postulate
  reify⋆ : ∀ {{_ : Model}} {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (lam t)           γ δ = λ ψ a → eval t (mono²⊩⋆ ψ γ , a) (mono²⊩⋆ ψ δ)
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval (mvar i)          γ δ = mlookup i δ
eval (box t)           γ δ = λ ψ → let δ′ = mono²⊩⋆ ψ δ
                                    in  mmulticut (reify⋆ δ′) (box t) ⅋
                                          eval t ∙ δ′
eval (unbox t u)       γ δ = eval u γ (δ , λ ψ →
                               let γ′ = mono²⊩⋆ ψ γ
                                   δ′ = mono²⊩⋆ ψ δ
                               in  multicut² (reify⋆ γ′) (reify⋆ δ′) t ⅋
                                     ⟪↓⟫ (eval t γ′ δ′))
eval (pair t u)        γ δ = eval t γ δ , eval u γ δ
eval (fst t)           γ δ = π₁ (eval t γ δ)
eval (snd t)           γ δ = π₂ (eval t γ δ)
eval unit              γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ Π P → Π ⊢ α P
      ; mono²⊩ᵅ = mono²⊢
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ ψ → let t′ = mono²⊢ ψ t
                              in  λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ ψ → let t′ = mono²⊢ ψ t
                              in  t′ ⅋ reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reifyᶜ {α P}   s = s
  reifyᶜ {A ▻ B} s = lam (reifyᶜ (s (weak⊆²₁) (reflectᶜ {A} v₀)))
  reifyᶜ {□ A}   s = syn (s refl⊆²)
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unit

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Ξ} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
