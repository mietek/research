module BasicIPC.Metatheory.Gentzen-TarskiCoquandDybjer where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiCoquandDybjer public

open ImplicitSyntax (_⊢_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ η → multicut (reify⋆ (mono⊩⋆ η γ)) (lam t) , λ a →
                      eval t (mono⊩⋆ η γ , a)
eval (app t u)  γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


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
reflectᶜ {α P}   t = t , t
reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                            in  t′ , λ a → reflectᶜ (app t′ (reify a))
reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
reflectᶜ {⊤}    t = ∙

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


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
