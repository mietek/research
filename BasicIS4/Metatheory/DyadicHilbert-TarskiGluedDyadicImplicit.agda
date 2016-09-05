module BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicImplicit where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiGluedDyadicImplicit public

open ImplicitSyntax (_⊢_) public


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ ψ = let t ⅋ s₁′ = s₁ ψ
                              u ⅋ a   = s₂ ψ
                          in  app (app cdist t) u ⅋ _⟪$⟫_ {A} {B} s₁′ a

  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = _⟪D⟫_ (mono²⊩ {□ (A ▻ B)} ψ s₁)

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ s ψ = app cup (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆² ψ ψ′)


-- Soundness with respect to all models, or evaluation.

-- FIXME
postulate
  reify⋆ : ∀ {{_ : Model}} {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval ci                γ δ = K I
eval (ck {A} {B})      γ δ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ δ = K (⟪S⟫′ {A} {B} {C})
eval (mvar i)          γ δ = mlookup i δ
eval (box t)           γ δ = λ ψ → let δ′ = mono²⊩⋆ ψ δ
                                    in  mmulticut (reify⋆ δ′) (box t) ⅋
                                          eval t ∙ δ′
eval cdist             γ δ = K _⟪D⟫′_
eval cup               γ δ = K ⟪↑⟫
eval cdown             γ δ = K ⟪↓⟫
eval (cpair {A} {B})   γ δ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ δ = K π₁
eval csnd              γ δ = K π₂
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
  reifyᶜ {A ▻ B} s = lam (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} v₀)))
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
