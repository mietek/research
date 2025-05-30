{-# OPTIONS --sized-types #-}

-- TODO

module A201607.WIP2.BasicIS4.Semantics.Sketch10 where

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

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : Cx² Ty Ty → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′} → w ⊆² w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′} → mod w ⊆ mod w′ → w′ ⊢ A × w′ ⊩ A
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙
--    w ⊪ ⊥    = 𝟘
--    w ⊪ A ∨ B = w ⊩ A ⊎ w ⊩ B

    infix 3 _⊩_
    _⊩_ : Cx² Ty Ty → Ty → Set
    w ⊩ A = ∀ {C w′} → w ⊆² w′ → (∀ {w″} → w′ ⊆² w″ → w″ ⊪ A → w″ ⊢ⁿᶠ C) → w′ ⊢ⁿᶠ C

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
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ∅ ⁏ mod w ⊢⋆ Δ → ∅ ⁏ mod w ⊩⋆ Δ → w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ∅ ⁏ mod w ⊢⋆ Δ → ∅ ⁏ mod w ⊩⋆ Δ → w ⊩⋆ Ξ


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

  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


-- Soundness with respect to all models, or evaluation.

-- box⋆ : ∀ {Ξ Γ Δ} → ∅ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢⋆ □⋆ Ξ
-- box⋆ {∅}     ∙        = ∙
-- box⋆ {Ξ , A} (ts , t) = box⋆ ts , box t

unbox⋆ : ∀ {Ξ C Γ Δ} → Γ ⁏ Δ ⊢⋆ □⋆ Ξ → Γ ⁏ Δ ⧺ Ξ ⊢ C → Γ ⁏ Δ ⊢ C
unbox⋆ {∅}     ∙        u = u
unbox⋆ {Ξ , A} (ts , t) u = unbox t (mdet (unbox⋆ ts (mlam u)))

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ ד δ = lookup i γ
eval (lam {A} {B} t)     γ ד δ = return {A ▻ B} λ { (η , θ) a →
                                   eval t (mono⊩⋆ (η , θ) γ , a)
                                          (mmono⊢⋆ θ ד)
                                          (mono⊩⋆ (refl⊆ , θ) δ) }
eval (app {A} {B} t u)   γ ד δ = bind {A ▻ B} {B} (eval t γ ד δ) λ { (η , θ) f →
                                   _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ (η , θ) γ)
                                                           (mmono⊢⋆ θ ד)
                                                           (mono⊩⋆ (refl⊆ , θ) δ)) }
eval (mvar {A} i)        γ ד δ = mono⊩ {A} (bot⊆ , refl⊆) (lookup i δ)
eval (box {A} t)         γ ד δ = return {□ A} λ θ →
                                   unbox⋆ (box⋆ (mmono⊢⋆ θ ד)) (mono²⊢ (bot⊆ , weak⊆⧺₂) t) ,
                                   eval t ∙
                                          (mmono⊢⋆ θ ד)
                                          (mono⊩⋆ (refl⊆ , θ) δ)
eval (unbox {A} {C} t u) γ ד δ = bind {□ A} {C} (eval t γ ד δ) λ { (η , θ) a →
                                   eval u (mono⊩⋆ (η , θ) γ)
                                          (mmono⊢⋆ θ ד , π₁ (a refl⊆))
                                          (mono⊩⋆ (refl⊆ , θ) δ , π₂ (a refl⊆)) }
eval (pair {A} {B} t u)  γ ד δ = return {A ∧ B} (eval t γ ד δ , eval u γ ד δ)
eval (fst {A} {B} t)     γ ד δ = bind {A ∧ B} {A} (eval t γ ד δ) (K π₁)
eval (snd {A} {B} t)     γ ד δ = bind {A ∧ B} {B} (eval t γ ד δ) (K π₂)
eval unit                γ ד δ = return {⊤} ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ ד δ = ∙
eval⋆ {Ξ , A} (ts , t) γ ד δ = eval⋆ ts γ ד δ , eval t γ ד δ


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊪ᵅ_   = λ Π P → Π ⊢ⁿᵉ α P
      ; mono⊪ᵅ = mono²⊢ⁿᵉ
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
  reifyᶜ {□ A}   k = k refl⊆² λ ξ s → boxⁿᶠ (π₁ (s refl⊆))
  reifyᶜ {A ∧ B} k = k refl⊆² λ ξ s → pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    k = k refl⊆² λ ξ s → unitⁿᶠ

  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = return {α P} t
  reflectᶜ {A ▻ B} t = return {A ▻ B} λ { (η , θ) a →
                         reflectᶜ {B} (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
  reflectᶜ {□ A}   t = λ { (η , θ) k →
                         neⁿᶠ (unboxⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (k (refl⊆ , weak⊆) λ θ′ →
                           mvar (grab∈ θ′) , reflectᶜ {A} (mvarⁿᵉ (grab∈ θ′)))) }
  reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t))
  reflectᶜ {⊤}    t = return {⊤} ∙

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- TODO

mrefl⊢⋆ⁿᵉ : ∀ {Δ} → ∅ ⁏ Δ ⊢⋆ⁿᵉ Δ
mrefl⊢⋆ⁿᵉ {∅}     = ∙
mrefl⊢⋆ⁿᵉ {Γ , A} = mmono⊢⋆ⁿᵉ weak⊆ mrefl⊢⋆ⁿᵉ , mvarⁿᵉ top


-- Reflexivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

mrefl⊩⋆ : ∀ {Δ} → ∅ ⁏ Δ ⊩⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆ⁿᵉ


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊢⋆″ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
norm = quot ∘ eval
