module BasicIS4.Metatheory.Gentzen-TarskiOvergluedImplicit where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiOvergluedImplicit public

open ImplicitSyntax (_⊢_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ in t
  reify {□ A}   s       = let t , f = s refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ η → let γ′ = mono⊩⋆ η γ
                                  in  multicut (reify⋆ γ′) (lam t) , λ a →
                                        eval t (γ′ , a)
  eval (app t u)       γ = eval t γ ⟪$⟫ eval u γ
  eval (multibox ts u) γ = λ η → let γ′ = mono⊩⋆ η γ
                                  in  multicut (reify⋆ γ′) (multibox ts u) ,
                                        eval u (eval⋆ ts γ′)
  eval (down t)        γ = ⟪↓⟫ (eval t γ)
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


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
reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                            in  t′ , reflectᶜ (down t′)
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
