module BasicIS4.Metatheory.DyadicHilbert-TarskiGluedDyadicHilbert where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiGluedDyadicHilbert public


-- Soundness with respect to the syntax representation in a particular model.

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
  [ tt ]      = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)           γ δ = lookup i γ
eval (app {A} {B} t u) γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval ci                γ δ = K I
eval (ck {A} {B})      γ δ = K (⟪K⟫ {A} {B})
eval (cs {A} {B} {C})  γ δ = K (⟪S⟫′ {A} {B} {C})
eval (mvar i)          γ δ = mlookup i δ
eval (box t)           γ δ = λ η → [ box t ] ,
                               eval t ∙ (mono⊩⋆ η δ)
eval cdist             γ δ = K _⟪D⟫′_
eval cup               γ δ = K ⟪↑⟫
eval cdown             γ δ = K ⟪↓⟫
eval (cpair {A} {B})   γ δ = K (_⟪,⟫′_ {A} {B})
eval cfst              γ δ = K π₁
eval csnd              γ δ = K π₂
eval tt                γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⁏_⊩ᵅ_  = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
      ; mono⊩ᵅ  = mono⊢
      ; _⁏_[⊢]_ = _⁏_⊢_
      ; mono[⊢] = mono⊢
      ; [var]    = var
      ; [app]    = app
      ; [ci]     = ci
      ; [ck]     = ck
      ; [cs]     = cs
      ; [mvar]   = mvar
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
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                              in  t′ , reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reifyᶜ {α P}   s       = s
  reifyᶜ {A ▻ B} s       = lam (reifyᶜ (s weak⊆ (reflectᶜ {A} v₀)))
  reifyᶜ {□ A}   s       = let t , a = s refl⊆ in t
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Π} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Π → Γ ⁏ Δ ⊩⋆ Π
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
