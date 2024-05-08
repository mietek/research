{-# OPTIONS --allow-unsolved-metas #-}

-- TODO

module A201607.WIP2.BasicIS4.Semantics.Sketch where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public
open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public


-- Intuitionistic modal Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx² Ty Ty → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ⊆² w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

open Model {{…}} public


{-

TODO: Define the model properly so that syntax is internalised and not completely implicit.

Canonical _≤_ should be:
- Any Γ such that Γʷ ⊆ Γ
- Any Δ such that Δʷ ⊆ Δ

Canonical _R_ should be:
- Any Γ whatsoever; means we must deal with loss of non-modal assumptions
- Any Δ such that Δʷ ⊆ Δ

-}

-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx² Ty Ty → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▻ B = ∀ {w′} → w ⊆² w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A   = ∀ {w′} → mod w ⊆ mod w′ → w′ ⊢ A
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx² Ty Ty → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ⊆² w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ       s = mono⊩ᵅ ξ s
  mono⊩ {A ▻ B} ξ       s = λ ξ′ a → s (trans⊆² ξ ξ′) a
  mono⊩ {□ A}   (η , θ) s = λ θ′ → s (trans⊆ θ θ′)
  mono⊩ {A ∧ B} ξ       s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
  mono⊩ {⊤}    ξ       s = ∙

  mono⊩⋆ : ∀ {Ξ w w′} → w ⊆² w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Ξ , A} ξ (γ , a) = mono⊩⋆ {Ξ} ξ γ , mono⊩ {A} ξ a


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx² Ty Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ∅ ⁏ mod w ⊢⋆ Δ → w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ∅ ⁏ mod w ⊢⋆ Δ → w ⊩⋆ Ξ


-- TODO

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ w} → A ∈ Δ → w ⊢⋆ Δ → w ⊢ A
  mlookup top     (δ , a) = a
  mlookup (pop i) (δ , b) = mlookup i δ


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

-- TODO: ugh, do we need exploding worlds?

mutual
  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}   s = neⁿᶠ s
  reifyᶜ {A ▻ B} s = lamⁿᶠ (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {□ A}   s = boxⁿᶠ (s refl⊆)
  reifyᶜ {A ∧ B} s = pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    s = unitⁿᶠ

  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ { (η , θ) a → reflectᶜ (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
  reflectᶜ {□ A}   t = λ θ → {!neⁿᶠ ?!}
  reflectᶜ {A ∧ B} t = reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t)
  reflectᶜ {⊤}    t = ∙

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- Reflexivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊢⋆″)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
norm = quot ∘ eval
