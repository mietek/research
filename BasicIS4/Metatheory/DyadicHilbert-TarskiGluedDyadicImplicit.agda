module BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicImplicit where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiGluedDyadicImplicit public

open ImplicitSyntax (_⁏_⊢_) public


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ η = let t ⅋ s₁′ = s₁ η
                              u ⅋ a   = s₂ η
                          in  app (app cdist t) u ⅋ _⟪$⟫_ {A} {B} s₁′ a

  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ η = _⟪D⟫_ (mono⊩ {□ (A ▻ B)} η s₁)

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ s η = app cup (syn (s η)) ⅋ λ η′ → s (trans⊆ η η′)


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval ci                γ δ = K I
eval (ck {A} {B})      γ δ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ δ = K (⟪S⟫′ {A} {B} {C})
eval (mvar i)          γ δ = mlookup i δ
eval (box t)           γ δ = λ η → box t ⅋
                               eval t ∙ (mono⊩⋆ η δ)
eval cdist             γ δ = K _⟪D⟫′_
eval cup               γ δ = K ⟪↑⟫
eval cdown             γ δ = K ⟪↓⟫
eval (cpair {A} {B})   γ δ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ δ = K π₁
eval csnd              γ δ = K π₂
eval tt                γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⁏_⊩ᵅ_ = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
      ; mono⊩ᵅ = mono⊢
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                              in  t′ ⅋ reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reifyᶜ {α P}   s       = s
  reifyᶜ {A ▻ B} s       = lam (reifyᶜ (s weak⊆ (reflectᶜ {A} v₀)))
  reifyᶜ {□ A}   s       = syn (s refl⊆)
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
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
