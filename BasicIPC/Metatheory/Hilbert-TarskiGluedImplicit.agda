module BasicIPC.Metatheory.Hilbert-TarskiGluedImplicit where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiGluedImplicit public

open ImplicitSyntax (_⊢_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s       = syn s
  reify {A ▻ B} s       = syn (s refl⊆)
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪K⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪K⟫ {A} a η = let a′ = mono⊩ {A} η a
                in  app ck (reify a′) ⅋ K a′

  ⟪S⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ η = let s₁′ = mono⊩ {A ▻ B ▻ C} η s₁
                              t   = syn (s₁′ refl⊆)
                          in  app cs t ⅋ λ s₂ η′ →
                                let s₁″ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                    s₂′ = mono⊩ {A ▻ B} η′ s₂
                                    t′  = syn (s₁″ refl⊆)
                                    u   = syn (s₂′ refl⊆)
                                in  app (app cs t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η = let a′ = mono⊩ {A} η a
                   in  app cpair (reify a′) ⅋ _,_ a′


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = K (ci ⅋ I)
eval ck        γ = K (ck ⅋ ⟪K⟫)
eval cs        γ = K (cs ⅋ ⟪S⟫′)
eval cpair     γ = K (cpair ⅋ _⟪,⟫′_)
eval cfst      γ = K (cfst ⅋ π₁)
eval csnd      γ = K (csnd ⅋ π₂)
eval tt        γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ = mono⊢
      }


-- Soundness with respect to the canonical model.

reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
reflectᶜ {α P}   t = t ⅋ t
reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                            in  t′ ⅋ λ a → reflectᶜ (app t′ (reify a))
reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
reflectᶜ {⊤}    t = ∙

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reify (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
