{-# OPTIONS --sized-types #-}

-- TODO

module A201607.WIP2.BasicIS4.Semantics.Sketch2 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public
open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public


-- Intuitionistic modal Kripke models.

record Model : Set₁ where
  infix 3 _⊪ᵅ_
  field
    -- Strong forcing for atomic propositions; monotonic.
    _⊪ᵅ_   : Cx² Ty Ty → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w ⊆² w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

    -- Exploding.
    _‼_ : Cx² Ty Ty → Ty → Set

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
  mutual
    infix 3 _⊪_
    _⊪_ : Cx² Ty Ty → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′} → w ⊆² w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′} → mod w ⊆ mod w′ → w′ ⊢ A
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙
--    w ⊪ ⊥    = 𝟘
--    w ⊪ A ∨ B = w ⊩ A ⊎ w ⊩ B

    infix 3 _⊩_
    _⊩_ : Cx² Ty Ty → Ty → Set
    w ⊩ A = ∀ {C w′} → w ⊆² w′ → (∀ {w″} → w′ ⊆² w″ → w″ ⊪ A → w″ ‼ C) → w′ ‼ C

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx² Ty Ty → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mutual
    mono⊪ : ∀ {A w w′} → w ⊆² w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ       s = mono⊪ᵅ ξ s
    mono⊪ {A ▻ B} ξ       s = λ ξ′ a → s (trans⊆² ξ ξ′) a
    mono⊪ {□ A}   (η , θ) s = λ θ′ → s (trans⊆ θ θ′)
    mono⊪ {A ∧ B} ξ       s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
    mono⊪ {⊤}    ξ       s = ∙
--    mono⊪ {⊥}    ξ ()
--    mono⊪ {A ∨ B} ξ (ι₁ a)  = ι₁ (mono⊩ {A} ξ a)
--    mono⊪ {A ∨ B} ξ (ι₂ b)  = ι₂ (mono⊩ {B} ξ b)

    mono⊩ : ∀ {A w w′} → w ⊆² w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans⊆² ξ ξ′) k′

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


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B w} → w ⊪ A ▻ B → w ⊩ A → w ⊩ B
  s ⟪$⟫ a = s refl⊆² a

  return : ∀ {A w} → w ⊪ A → w ⊩ A
  return {A} a = λ ξ k → k refl⊆² (mono⊪ {A} ξ a)

  bind : ∀ {A B w} → w ⊩ A → (∀ {w′} → w ⊆² w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
  bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans⊆² ξ ξ′) a′ refl⊆² (λ ξ″ a″ → k′ (trans⊆² ξ′ ξ″) a″))


-- Soundness with respect to all models, or evaluation.

-- TODO: the mvar top case ruins the termination argument.

{-# TERMINATING #-}
eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ δ = lookup i γ
eval (lam {A} {B} t)     γ δ = return {A ▻ B} λ { (η , θ) a →
                                 eval t (mono⊩⋆ (η , θ) γ , a) (mmono⊢⋆ θ δ) }
eval (app {A} {B} t u)   γ δ = bind {A ▻ B} {B} (eval t γ δ) λ { (η , θ) f →
                                 _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ (η , θ) γ) (mmono⊢⋆ θ δ)) }
eval (mvar i)            γ δ = eval (mlookup i δ) ∙ mrefl⊢⋆″
eval (box {A} t)         γ δ = return {□ A} λ θ →
                                 mono⊢ bot⊆ (mmulticut′ (mmono⊢⋆ θ δ) t)
eval (unbox {A} {C} t u) γ δ = bind {□ A} {C} (eval t γ δ) λ { (η , θ) a →
                                 eval u (mono⊩⋆ (η , θ) γ) (mmono⊢⋆ θ δ , a refl⊆) }
eval (pair {A} {B} t u)  γ δ = return {A ∧ B} (eval t γ δ , eval u γ δ)
eval (fst {A} {B} t)     γ δ = bind {A ∧ B} {A} (eval t γ δ) (K π₁)
eval (snd {A} {B} t)     γ δ = bind {A ∧ B} {B} (eval t γ δ) (K π₂)
eval unit                γ δ = return {⊤} ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ δ = ∙
eval⋆ {Ξ , A} (ts , t) γ δ = eval⋆ ts γ δ , eval t γ δ


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊪ᵅ_   = λ Π P → Π ⊢ⁿᵉ α P
      ; mono⊪ᵅ = mono²⊢ⁿᵉ
      ; _‼_     = λ Π A → Π ⊢ⁿᶠ A
      }


-- Soundness and completeness with respect to the canonical model.

module _ {U : Set} where
  grab∈ : ∀ {A : U} {Γ Γ′} → Γ , A ⊆ Γ′ → A ∈ Γ′
  grab∈ (skip η) = pop (grab∈ η)
  grab∈ (keep η) = top

mutual
  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}   k = k refl⊆² λ ξ s → neⁿᶠ s
  reifyᶜ {A ▻ B} k = k refl⊆² λ ξ s → lamⁿᶠ (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {□ A}   k = k refl⊆² λ ξ s → boxⁿᶠ (s refl⊆)
  reifyᶜ {A ∧ B} k = k refl⊆² λ ξ s → pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    k = k refl⊆² λ ξ s → unitⁿᶠ

  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = return {α P} t
  reflectᶜ {A ▻ B} t = return {A ▻ B} λ { (η , θ) a →
                         reflectᶜ {B} (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
  reflectᶜ {□ A}   t = λ { (η , θ) k →
                         neⁿᶠ (unboxⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (k (refl⊆ , weak⊆) λ θ′ →
                           mvar (grab∈ θ′))) }
  reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t))
  reflectᶜ {⊤}    t = return {⊤} ∙

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
