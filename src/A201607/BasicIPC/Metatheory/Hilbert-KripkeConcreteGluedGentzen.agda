{-# OPTIONS --sized-types #-}

module A201607.BasicIPC.Metatheory.Hilbert-KripkeConcreteGluedGentzen where

open import A201607.BasicIPC.Syntax.Hilbert public
open import A201607.BasicIPC.Semantics.KripkeConcreteGluedGentzen public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ} → Γ ⊢ A → Γ [⊢] A
  [ var i ]   = [var] i
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ unit ]    = [unit]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = [ci] ⅋ K I
eval ck        γ = [ck] ⅋ K ⟪K⟫
eval cs        γ = [cs] ⅋ K ⟪S⟫′
eval cpair     γ = [cpair] ⅋ K _⟪,⟫′_
eval cfst      γ = [cfst] ⅋ K π₁
eval csnd      γ = [csnd] ⅋ K π₂
eval unit      γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ w P → unwrap w ⊢ α P
      ; mono⊩ᵅ  = λ ξ t → mono⊢ (unwrap≤ ξ) t
      ; _[⊢]_   = _⊢_
      ; mono[⊢] = mono⊢
      ; [var]    = var
      ; [lam]    = lam
      ; [app]    = app
      ; [pair]   = pair
      ; [fst]    = fst
      ; [snd]    = snd
      ; [unit]   = unit
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A w} → unwrap w ⊢ A → w ⊩ A
  reflectᶜ {α P}   t = t ⅋ t
  reflectᶜ {A ▻ B} t = t ⅋ λ ξ a → reflectᶜ (app (mono⊢ (unwrap≤ ξ) t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A w} → w ⊩ A → unwrap w ⊢ A
  reifyᶜ {α P}   s = syn s
  reifyᶜ {A ▻ B} s = syn s
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unit

reflectᶜ⋆ : ∀ {Ξ w} → unwrap w ⊢⋆ Ξ → w ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → unwrap w ⊢⋆ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {w} → w ⊩⋆ unwrap w
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {w w′ w″} → w ⊩⋆ unwrap w′ → w′ ⊩⋆ unwrap w″ → w ⊩⋆ unwrap w″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reifyᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
