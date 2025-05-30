{-# OPTIONS --sized-types #-}

module A201607.BasicIS4.Metatheory.DyadicHilbert-TarskiOvergluedDyadicHilbert where

open import A201607.BasicIS4.Syntax.DyadicHilbert public
open import A201607.BasicIS4.Semantics.TarskiOvergluedDyadicHilbert public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]   = [var] i
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ mvar i ]  = [mvar] i
  [ box t ]   = [box] [ t ]
  [ cdist ]   = [cdist]
  [ cup ]     = [cup]
  [ cdown ]   = [cdown]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ unit ]    = [unit]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci        γ δ = K ([ci] ⅋ I)
eval ck        γ δ = K ([ck] ⅋ ⟪K⟫)
eval cs        γ δ = K ([cs] ⅋ ⟪S⟫′)
eval (mvar i)  γ δ = mlookup i δ
eval (box t)   γ δ = λ ψ → let δ′ = mono²⊩⋆ ψ δ
                            in  [mmulticut] (reifyʳ⋆ δ′) [ box t ] ⅋
                                  eval t ∙ δ′
eval cdist     γ δ = K ([cdist] ⅋ _⟪D⟫′_)
eval cup       γ δ = K ([cup] ⅋ ⟪↑⟫)
eval cdown     γ δ = K ([cdown] ⅋ ⟪↓⟫)
eval cpair     γ δ = K ([cpair] ⅋ _⟪,⟫′_)
eval cfst      γ δ = K ([cfst] ⅋ π₁)
eval csnd      γ δ = K ([csnd] ⅋ π₂)
eval unit      γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_     = λ Π P → Π ⊢ α P
      ; mono²⊩ᵅ  = mono²⊢
      ; _[⊢]_    = _⊢_
      ; mono²[⊢] = mono²⊢
      ; [var]     = var
      ; [app]     = app
      ; [ci]      = ci
      ; [ck]      = ck
      ; [cs]      = cs
      ; [mvar]    = mvar
      ; [box]     = box
      ; [cdist]   = cdist
      ; [cup]     = cup
      ; [cdown]   = cdown
      ; [cpair]   = cpair
      ; [cfst]    = cfst
      ; [csnd]    = csnd
      ; [unit]    = unit
      ; [mlam]    = mlam
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t ⅋ t
  reflectᶜ {A ▻ B} t = λ ψ → let t′ = mono²⊢ ψ t
                              in  t′ ⅋ λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ ψ → let t′ = mono²⊢ ψ t
                              in  t′ ⅋ reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reifyᶜ {α P}   s = syn s
  reifyᶜ {A ▻ B} s = syn (s refl⊆²)
  reifyᶜ {□ A}   s = syn (s refl⊆²)
  reifyᶜ {A ∧ B} s = pair (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unit

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Ξ} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
