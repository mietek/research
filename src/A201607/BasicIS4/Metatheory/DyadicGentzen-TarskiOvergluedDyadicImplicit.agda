module A201607.BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicImplicit where

open import A201607.BasicIS4.Syntax.DyadicGentzen public
open import A201607.BasicIS4.Semantics.TarskiOvergluedDyadicImplicit public

open ImplicitSyntax (_⊢_) (mono²⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reify {α P}   s = syn s
  reify {A ▻ B} s = syn (s refl⊆²)
  reify {□ A}   s = syn (s refl⊆²)
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
  reify {⊤}    s = unit

  reify⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
  reify⋆ {∅}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ ψ → let γ′ = mono²⊩⋆ ψ γ in
                              let δ′ = mono²⊩⋆ ψ δ
                              in  multicut² (reify⋆ γ′) (reify⋆ δ′) (lam t) ⅋ λ a →
                                    eval t (γ′ , a) δ′
eval (app t u)   γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval (mvar i)    γ δ = mlookup i δ
eval (box t)     γ δ = λ ψ → let γ′ = mono²⊩⋆ ψ γ in
                              let δ′ = mono²⊩⋆ ψ δ
                              in  multicut² (reify⋆ γ′) (reify⋆ δ′) (box t) ⅋
                                    eval t ∙ δ′
eval (unbox t u) γ δ = eval u γ (δ , eval t γ δ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval unit        γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ Π P → Π ⊢ α P
      ; mono²⊩ᵅ = mono²⊢
      }


-- Soundness with respect to the canonical model.

reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
reflectᶜ {α P}   t = t ⅋ t
reflectᶜ {A ▻ B} t = λ ψ → let t′ = mono²⊢ ψ t
                            in  t′ ⅋ λ a → reflectᶜ (app t′ (reify a))
reflectᶜ {□ A}   t = λ ψ → let t′ = mono²⊢ ψ t
                            in  t′ ⅋ reflectᶜ (down t′)
reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
reflectᶜ {⊤}    t = ∙

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Ξ} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reify (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
