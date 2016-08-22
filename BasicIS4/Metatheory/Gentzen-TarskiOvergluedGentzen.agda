module BasicIS4.Metatheory.Gentzen-TarskiOvergluedGentzen where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiOvergluedGentzen public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  mutual
    [_] : ∀ {A Γ} → Γ ⊢ A → Γ [⊢] A
    [ var i ]         = [var] i
    [ lam t ]         = [lam] [ t ]
    [ app t u ]       = [app] [ t ] [ u ]
    [ multibox ts u ] = [multibox] ([⊢]⋆→[⊢⋆] [ ts ]⋆) [ u ]
    [ down t ]        = [down] [ t ]
    [ pair t u ]      = [pair] [ t ] [ u ]
    [ fst t ]         = [fst] [ t ]
    [ snd t ]         = [snd] [ t ]
    [ tt ]            = [tt]

    [_]⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ [⊢]⋆ Ξ
    [_]⋆ {⌀}     ∙        = ∙
    [_]⋆ {Ξ , A} (ts , t) = [ ts ]⋆ , [ t ]


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ η → let γ′ = mono⊩⋆ η γ
                                  in  [multicut] (reifyʳ⋆ γ′) [ lam t ] ⅋ λ a →
                                        eval t (γ′ , a)
  eval (app t u)       γ = eval t γ ⟪$⟫ eval u γ
  eval (multibox ts u) γ = λ η → let γ′ = mono⊩⋆ η γ
                                  in  [multicut] (reifyʳ⋆ γ′) [ multibox ts u ] ⅋
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
      { _⊩ᵅ_      = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ    = mono⊢
      ; _[⊢]_     = _⊢_
      ; _[⊢⋆]_    = _⊢⋆_
      ; mono[⊢]   = mono⊢
      ; [var]      = var
      ; [lam]      = lam
      ; [app]      = app
      ; [multibox] = multibox
      ; [down]     = down
      ; [pair]     = pair
      ; [fst]      = fst
      ; [snd]      = snd
      ; [tt]       = tt
      ; top[⊢⋆]   = refl
      ; pop[⊢⋆]   = refl
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = t ⅋ t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  t′ ⅋ λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                              in  t′ ⅋ reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   s = syn s
  reifyᶜ {A ▻ B} s = syn (s refl⊆)
  reifyᶜ {□ A}   s = syn (s refl⊆)
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = tt

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reifyᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
