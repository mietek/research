module BasicIS4.Metatheory.DyadicGentzen-TarskiOvergluedDyadicImplicit where

open import BasicIS4.Syntax.DyadicGentzen public
open import BasicIS4.Semantics.TarskiOvergluedDyadicImplicit public

open ImplicitSyntax (_⁏_⊢_) (mono⊢) (mmono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reify {□ A}   s       = let t , a = s refl⊆ refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ η θ → let γ′ = mono²⊩⋆ (η , θ) γ in
                                let δ′ = mono²⊩⋆ (η , θ) δ
                                in  multicut² (reify⋆ γ′) (reify⋆ δ′) (lam t) , λ a →
                                      eval t (γ′ , a) δ′
eval (app t u)   γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval (mvar i)    γ δ = mlookup i δ
eval (box t)     γ δ = λ η θ → let γ′ = mono²⊩⋆ (η , θ) γ in
                                let δ′ = mono²⊩⋆ (η , θ) δ
                                in  multicut² (reify⋆ γ′) (reify⋆ δ′) (box t) ,
                                      eval t ∙ δ′
eval (unbox t u) γ δ = eval u γ (δ , eval t γ δ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⁏_⊩ᵅ_  = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
      ; mono⊩ᵅ  = mono⊢
      ; mmono⊩ᵅ = mmono⊢
      }


-- Soundness with respect to the canonical model.

reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
reflectᶜ {α P}   t = t , t
reflectᶜ {A ▻ B} t = λ η θ → let t′ = mono²⊢ (η , θ) t
                              in  t′ , λ a → reflectᶜ (app t′ (reify a))
reflectᶜ {□ A}   t = λ η θ → let t′ = mono²⊢ (η , θ) t
                              in  t′ , reflectᶜ (down t′)
reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
reflectᶜ {⊤}    t = ∙

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
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
