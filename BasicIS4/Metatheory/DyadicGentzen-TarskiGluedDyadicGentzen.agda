module BasicIS4.Metatheory.DyadicGentzen-TarskiGluedDyadicGentzen where

open import BasicIS4.Syntax.DyadicGentzen public
open import BasicIS4.Semantics.TarskiGluedDyadicGentzen public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]     = [var] i
  [ lam t ]     = [lam] [ t ]
  [ app t u ]   = [app] [ t ] [ u ]
  [ mvar i ]    = [mvar] i
  [ box t ]     = [box] [ t ]
  [ unbox t u ] = [unbox] [ t ] [ u ]
  [ pair t u ]  = [pair] [ t ] [ u ]
  [ fst t ]     = [fst] [ t ]
  [ snd t ]     = [snd] [ t ]
  [ tt ]        = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ δ = lookup i γ
eval (lam t)             γ δ = λ η a → eval t (mono⊩⋆ η γ , a) (mono⊩⋆ η δ)
eval (app {A} {B} t u)   γ δ = _⟪$⟫_ {A} {B} (eval t γ δ) (eval u γ δ)
eval (mvar i)            γ δ = mlookup i δ
eval (box t)             γ δ = λ η → [ box t ] ,
                                 eval t ∙ (mono⊩⋆ η δ)
eval (unbox {A} {C} t u) γ δ = let a = ⟪↓⟫ {A} (eval t γ δ)
                               in  {!δ , a !}
eval (pair t u)          γ δ = eval t γ δ , eval u γ δ
eval (fst t)             γ δ = π₁ (eval t γ δ)
eval (snd t)             γ δ = π₂ (eval t γ δ)
eval tt                  γ δ = ∙


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
      ; [lam]    = lam
      ; [app]    = app
      ; [mvar]   = mvar
      ; [box]    = box
      ; [unbox]  = unbox
      ; [pair]   = pair
      ; [fst]    = fst
      ; [snd]    = snd
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

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
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
