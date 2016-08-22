module BasicIS4.Metatheory.Hilbert-TarskiOvergluedGentzen where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiOvergluedGentzen public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ} → Γ ⊢ A → Γ [⊢] A
  [ var i ]   = [var] i
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ box t ]   = [box] [ t ]
  [ cdist ]   = [cdist]
  [ cup ]     = [cup]
  [ cdown ]   = [cdown]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ tt ]      = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = K ([ ci ] ⅋ I)
eval ck        γ = K ([ ck ] ⅋ ⟪K⟫)
eval cs        γ = K ([ cs ] ⅋ ⟪S⟫′)
eval (box t)   γ = K ([ box t ] ⅋ eval t ∙)
eval cdist     γ = K ([ cdist ] ⅋ _⟪D⟫′_)
eval cup       γ = K ([ cup ] ⅋ ⟪↑⟫)
eval cdown     γ = K ([ cdown ] ⅋ ⟪↓⟫)
eval cpair     γ = K ([ cpair ] ⅋ _⟪,⟫′_)
eval cfst      γ = K ([ cfst ] ⅋ π₁)
eval csnd      γ = K ([ csnd ] ⅋ π₂)
eval tt        γ = ∙


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
  reifyᶜ {α P}   s       = syn s
  reifyᶜ {A ▻ B} s       = syn (s refl⊆)
  reifyᶜ {□ A}   s       = syn (s refl⊆)
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


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
