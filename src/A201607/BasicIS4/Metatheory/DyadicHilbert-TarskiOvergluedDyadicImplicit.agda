{-# OPTIONS --sized-types #-}

module A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicImplicit where

open import A201607.BasicIS4.Syntax.DyadicHilbert public
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


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪K⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A
  ⟪K⟫ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                in  app ck (reify a′) ⅋ K a′

  ⟪S⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ψ = let s₁′ = mono²⊩ {A ▻ B ▻ C} ψ s₁
                              t   = syn (s₁′ refl⊆²)
                          in  app cs t ⅋ λ s₂ ψ′ →
                                let s₁″ = mono²⊩ {A ▻ B ▻ C} (trans⊆² ψ ψ′) s₁
                                    s₂′ = mono²⊩ {A ▻ B} ψ′ s₂
                                    t′  = syn (s₁″ refl⊆²)
                                    u   = syn (s₂′ refl⊆²)
                                in  app (app cs t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  (s₁ ⟪D⟫ s₂) ψ = let t ⅋ s₁′ = s₁ ψ
                      u ⅋ a   = s₂ ψ
                  in  app (app cdist t) u ⅋ s₁′ ⟪$⟫ a

  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = let s₁′ = mono²⊩ {□ (A ▻ B)} ψ s₁
                        in  app cdist (reify (λ {_} ψ′ → s₁′ ψ′)) ⅋ _⟪D⟫_ s₁′

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ {A} s ψ = app cup (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆² ψ ψ′)

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                   in  app cpair (reify a′) ⅋ _,_ a′


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci        γ δ = K (ci ⅋ I)
eval ck        γ δ = K (ck ⅋ ⟪K⟫)
eval cs        γ δ = K (cs ⅋ ⟪S⟫′)
eval (mvar i)  γ δ = mlookup i δ
eval (box t)   γ δ = λ ψ → let δ′ = mono²⊩⋆ ψ δ
                            in  mmulticut (reify⋆ δ′) (box t) ⅋
                                  eval t ∙ δ′
eval cdist     γ δ = K (cdist ⅋ _⟪D⟫′_)
eval cup       γ δ = K (cup ⅋ ⟪↑⟫)
eval cdown     γ δ = K (cdown ⅋ ⟪↓⟫)
eval cpair     γ δ = K (cpair ⅋ _⟪,⟫′_)
eval cfst      γ δ = K (cfst ⅋ π₁)
eval csnd      γ δ = K (csnd ⅋ π₂)
eval unit      γ δ = ∙


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
