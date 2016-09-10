module BasicIPC.Metatheory.Hilbert-TarskiGluedImplicit where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiGluedImplicit public

open ImplicitSyntax (_⊢_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A w} → w ⊩ A → unwrap w ⊢ A
  reify {α P}   s = syn s
  reify {A ▻ B} s = syn (s refl≤)
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
  reify {⊤}    s = unit

  reify⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → unwrap w ⊢⋆ Ξ
  reify⋆ {∅}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪K⟫ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A
  ⟪K⟫ {A} a ξ = let a′ = mono⊩ {A} ξ a
                in  app ck (reify a′) ⅋ K a′

  ⟪S⟫′ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ξ = let s₁′ = mono⊩ {A ▻ B ▻ C} ξ s₁
                              t   = syn (s₁′ refl≤)
                          in  app cs t ⅋ λ s₂ ξ′ →
                                let s₁″ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) s₁
                                    s₂′ = mono⊩ {A ▻ B} ξ′ s₂
                                    t′  = syn (s₁″ refl≤)
                                    u   = syn (s₂′ refl≤)
                                in  app (app cs t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪,⟫′_ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a ξ = let a′ = mono⊩ {A} ξ a
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
eval unit      γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ w P → unwrap w ⊢ α P
      ; mono⊩ᵅ = λ ξ t → mono⊢ (unwrap≤ ξ) t
      }


-- Soundness with respect to the canonical model.

reflectᶜ : ∀ {A w} → unwrap w ⊢ A → w ⊩ A
reflectᶜ {α P}   t = t ⅋ t
reflectᶜ {A ▻ B} t = λ ξ → let t′ = mono⊢ (unwrap≤ ξ) t
                            in  t′ ⅋ λ a → reflectᶜ (app t′ (reify a))
reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
reflectᶜ {⊤}    t = ∙

reflectᶜ⋆ : ∀ {Ξ w} → unwrap w ⊢⋆ Ξ → w ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {w} → w ⊩⋆ unwrap w
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {w w′ w″} → w ⊩⋆ unwrap w′ → w′ ⊩⋆ unwrap w″ → w ⊩⋆ unwrap w″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reify (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
