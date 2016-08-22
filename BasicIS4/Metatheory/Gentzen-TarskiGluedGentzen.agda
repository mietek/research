module BasicIS4.Metatheory.Gentzen-TarskiGluedGentzen where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiGluedGentzen public


-- Soundness with respect to the syntax representation in a particular model.

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

    [_]⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ [⊢]⋆ Π
    [_]⋆ {⌀}     ∙        = ∙
    [_]⋆ {Π , A} (ts , t) = [ ts ]⋆ , [ t ]


-- TODO

module _ {{_ : Model}} where
  mutual
    reflectʳ : ∀ {A Γ} → Γ [⊢] A → Γ ⊩ A
    reflectʳ {α P}   t = {!!}
    reflectʳ {A ▻ B} t = λ η → let t′ = mono[⊢] η t
                                in  λ a → reflectʳ ([app] t′ (reifyʳ a))
    reflectʳ {□ A}   t = λ η → let t′ = mono[⊢] η t
                                in  t′ , reflectʳ ([down] t′)
    reflectʳ {A ∧ B} t = reflectʳ ([fst] t) , reflectʳ ([snd] t)
    reflectʳ {⊤}    t = ∙

    reifyʳ : ∀ {A Γ} → Γ ⊩ A → Γ [⊢] A
    reifyʳ {α P}   s       = {!!}
    reifyʳ {A ▻ B} s       = [lam] (reifyʳ (s weak⊆ (reflectʳ {A} ([var] top))))
    reifyʳ {□ A}   s       = let t , f = s refl⊆ in t
    reifyʳ {A ∧ B} (a , b) = [pair] (reifyʳ {A} a) (reifyʳ {B} b)
    reifyʳ {⊤}    ∙       = [tt]

  reifyʳ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ [⊢]⋆ Π
  reifyʳ⋆ {⌀}     ∙        = ∙
  reifyʳ⋆ {Π , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)           γ = lookup i γ
  eval (lam t)           γ = λ η a → eval t (mono⊩⋆ η γ , a)
  eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
  eval (multibox ts u)   γ = λ η → let γ′ = mono⊩⋆ η γ
                                    in  [multicut] (reifyʳ⋆ γ′) [ multibox ts u ] ,
                                          eval u (eval⋆ ts (mono⊩⋆ η γ))
  eval (down t)          γ = ⟪↓⟫ (eval t γ)
  eval (pair t u)        γ = eval t γ , eval u γ
  eval (fst t)           γ = π₁ (eval t γ)
  eval (snd t)           γ = π₂ (eval t γ)
  eval tt                γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


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
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                              in  t′ , reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   s       = s
  reifyᶜ {A ▻ B} s       = lam (reifyᶜ (s weak⊆ (reflectᶜ {A} v₀)))
  reifyᶜ {□ A}   s       = let t , a = s refl⊆ in t
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


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
