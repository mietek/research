{-# OPTIONS --allow-unsolved-metas #-}

module A201607.WIP2.BasicIS4.Metatheory.Sketch where

open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public
open import A201607.WIP2.BasicIS4.Semantics.Sketch public
  using (Model ; _⊩_ ; _⊩⋆_ ; mono⊩ ; mono⊩⋆ ; _⊨_ ; _⊨⋆_ ; lookup ; mlookup)


-- Cut and multicut, again.

cut′ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ B
cut′ t u = [ top ≔ t ] u

mcut′ : ∀ {A B Γ Δ} → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ , A ⊢ B → Γ ⁏ Δ ⊢ B
mcut′ t u = m[ top ≔ t ] u

extend : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ , A ⁏ Δ ⊢⋆ Ξ , A
extend {∅}     ∙        = ∙ , v₀
extend {Ξ , B} (ts , t) = mono⊢⋆ weak⊆ ts , mono⊢ weak⊆ t , v₀

mextend : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ , A ⊢⋆ Ξ , A
mextend {∅}     ∙        = ∙ , mv₀
mextend {Ξ , B} (ts , t) = mmono⊢⋆ weak⊆ ts , mmono⊢ weak⊆ t , mv₀

wat : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → A ∈ Ξ → Γ ⁏ Δ ⊢ A
wat {∅}     ∙        ()
wat {Ξ , B} (ts , t) top     = t
wat {Ξ , B} (ts , t) (pop i) = wat ts i

mwat : ∀ {Ξ A Γ Δ} → ∅ ⁏ Δ ⊢⋆ Ξ → A ∈ Ξ → Γ ⁏ Δ ⊢ A
mwat {∅}     ∙        ()
mwat {Ξ , B} (ts , t) top     = mono⊢ bot⊆ t
mwat {Ξ , B} (ts , t) (pop i) = mwat ts i

multicut′ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Ξ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
multicut′ ts (var i)     = wat ts i
multicut′ ts (lam u)     = lam (multicut′ (extend ts) u)
multicut′ ts (app u v)   = app (multicut′ ts u) (multicut′ ts v)
multicut′ ts (mvar i)    = mvar i
multicut′ ts (box u)     = box u
multicut′ ts (unbox u v) = unbox (multicut′ ts u) (multicut′ (mmono⊢⋆ weak⊆ ts) v)
multicut′ ts (pair u v)  = pair (multicut′ ts u) (multicut′ ts v)
multicut′ ts (fst u)     = fst (multicut′ ts u)
multicut′ ts (snd u)     = snd (multicut′ ts u)
multicut′ ts unit        = unit

mmulticut′ : ∀ {Ξ A Γ Δ} → ∅ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Ξ ⊢ A → Γ ⁏ Δ ⊢ A
mmulticut′ ts (var i)     = var i
mmulticut′ ts (lam u)     = lam (mmulticut′ ts u)
mmulticut′ ts (app u v)   = app (mmulticut′ ts u) (mmulticut′ ts v)
mmulticut′ ts (mvar i)    = mwat ts i
mmulticut′ ts (box u)     = box (mmulticut′ ts u)
mmulticut′ ts (unbox u v) = unbox (mmulticut′ ts u) (mmulticut′ (mextend ts) v)
mmulticut′ ts (pair u v)  = pair (mmulticut′ ts u) (mmulticut′ ts v)
mmulticut′ ts (fst u)     = fst (mmulticut′ ts u)
mmulticut′ ts (snd u)     = snd (mmulticut′ ts u)
mmulticut′ ts unit        = unit


-- Reflexivity, again.

mrefl⊢⋆″ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ Δ
mrefl⊢⋆″ {∅}     = ∙
mrefl⊢⋆″ {Δ , A} = mmono⊢⋆ weak⊆ mrefl⊢⋆″ , mv₀


-- Soundness with respect to all models, or evaluation.

-- TODO: the mvar top case ruins the termination argument.

{-# TERMINATING #-}
eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ { (η , θ) a → eval t (mono⊩⋆ (η , θ) γ , a) (mmono⊢⋆ θ δ) }
eval (app t u)   γ δ = (eval t γ δ refl⊆²) (eval u γ δ)
eval (mvar i)    γ δ = eval (mlookup i δ) ∙ mrefl⊢⋆″
eval (box t)     γ δ = λ θ → mono⊢ bot⊆ (mmulticut′ (mmono⊢⋆ θ δ) t)
eval (unbox t u) γ δ = eval u γ (δ , eval t γ δ refl⊆)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval unit        γ δ = ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ δ = ∙
eval⋆ {Ξ , A} (ts , t) γ δ = eval⋆ ts γ δ , eval t γ δ


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ Π P → Π ⊢ⁿᵉ α P
      ; mono⊩ᵅ = mono²⊢ⁿᵉ
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ { (η , θ) a → reflectᶜ (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
  reflectᶜ {□ A}   t = λ θ → {!neⁿᶠ ?!}
  reflectᶜ {A ∧ B} t = reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}   s = neⁿᶠ s
  reifyᶜ {A ▻ B} s = lamⁿᶠ (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {□ A}   s = boxⁿᶠ (s refl⊆)
  reifyᶜ {A ∧ B} s = pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unitⁿᶠ

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊢⋆″)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
norm = quot ∘ eval
