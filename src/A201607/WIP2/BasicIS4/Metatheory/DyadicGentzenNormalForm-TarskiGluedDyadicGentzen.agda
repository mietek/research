{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module A201607.WIP2.BasicIS4.Metatheory.DyadicGentzenNormalForm-TarskiGluedDyadicGentzen where

open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public
open import A201607.BasicIS4.Semantics.TarskiGluedDyadicGentzen public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]     = [var] i
  [ lam t ]     = [lam] [ t ]
  [ app t u ]   = [app] [ t ] [ u ]
  [ mvar i ]    = [mvar] i
  [ box t ]     = [box] [ t ]
  [ unbox t u ] = [unbox] [ t ] [ u ]
  [ pair t u ]  = [pair] [ t ] [ u ]
  [ fst t ]     = [fst] [ t ]
  [ snd t ]     = [snd] [ t ]
  [ unit ]      = [unit]


-- TODO: unfinished

-- Soundness with respect to all models, or evaluation.

eval : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ δ = lookup i γ
eval (lam t)             γ δ = λ ψ a → eval t (mono²⊩⋆ ψ γ , a) (mono²⊩⋆ ψ δ)
eval (app {A} {B} t u)   γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval (mvar i)            γ δ = {!!}
eval (box t)             γ δ = {![ t ]!}
eval (unbox {A} {C} t u) γ δ = {!!}
eval (pair t u)          γ δ = eval t γ δ , eval u γ δ
eval (fst t)             γ δ = π₁ (eval t γ δ)
eval (snd t)             γ δ = π₂ (eval t γ δ)
eval unit                γ δ = ∙
