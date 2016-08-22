module BasicIS4.Metatheory.Hilbert-TarskiGluedHilbert where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiGluedHilbert public


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
eval (var i)           γ = lookup i γ
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval ci                γ = K I
eval (ck {A} {B})      γ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ = K (⟪S⟫′ {A} {B} {C})
eval (box t)           γ = K ([ box t ] , eval t ∙)
eval cdist             γ = K _⟪D⟫′_
eval cup               γ = K ⟪↑⟫
eval cdown             γ = K ⟪↓⟫
eval (cpair {A} {B})   γ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ = K π₁
eval csnd              γ = K π₂
eval tt                γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ  = mono⊢
      ; _[⊢]_   = _⊢_
      ; mono[⊢] = mono⊢
      ; [var]    = var
      ; [app]    = app
      ; [ci]     = ci
      ; [ck]     = ck
      ; [cs]     = cs
      ; [box]    = box
      ; [cdist]  = cdist
      ; [cup]    = cup
      ; [cdown]  = cdown
      ; [cpair]  = cpair
      ; [cfst]   = cfst
      ; [csnd]   = csnd
      ; [tt]     = tt
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
