module New.BasicIS4.Metatheory.OpenDyadicGentzen-KripkeOno where

open import New.BasicIS4.Syntax.OpenDyadicGentzen public
open import New.BasicIS4.Semantics.KripkeOno public
open import New.BasicIS4.Semantics.KripkeDyadicCanonicalModelEquipment public

open SyntacticComponent (_⁏_⊢_) (mono²⊢) (up) (down) (lift) public


eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ ξ a → eval t (mono⊩⋆ ξ γ , a) (λ ζ → δ (transR (≤→R ξ) ζ))
eval (app t u)   γ δ = (eval t γ δ refl≤) (eval u γ δ)
eval (mvar i)    γ δ = lookup i (δ reflR)
eval (box t)     γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
eval (unbox t u) γ δ = eval u γ (λ ζ → δ ζ , (eval t γ δ) ζ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙


-- The canonical model.

instance
  canon : Model
  canon = record
    { World    = Worldᶜ
    ; _≤_      = _≤ᶜ_
    ; refl≤    = refl≤ᶜ
    ; trans≤   = trans≤ᶜ
    ; _R_      = _Rᶜ_
    ; reflR    = reflRᶜ
    ; transR   = transRᶜ
    ; _⊩ᵅ_    = λ { (Γ , Δ) P → Γ ⁏ Δ ⊢ α P }
    ; mono⊩ᵅ  = mono²⊢
    ; ≤⨾R→R   = ≤⨾R→Rᶜ
    }


-- Soundness and completeness with respect to the canonical model.

--- FIXME: Can we make this true?
postulate
  oops : ∀ {Γ Δ} → (Γ , Δ) Rᶜ (⌀ , Δ)

mutual
  reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , Δ ⊩ A
  reflect {α P}   t = t
  reflect {A ▻ B} t = λ ξ a → reflect {B} (app (mono²⊢ ξ t) (reify {A} a))
  reflect {□ A}   t = λ ζ → reflect {A} (ζ t)
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ Δ} → Γ , Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reify {α P}   s = s
  reify {A ▻ B} s = lam (reify {B} (s weak⊆²ₗ (reflect {A} v₀)))
  reify {□ A}   s = box (reify {A} (s oops))
  reify {A ∧ B} s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}    s = tt

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ , Δ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ Δ} → Γ , Δ ⊩⋆ Π → Γ ⁏ Δ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ Γ ⧺ (□⋆ Δ)
refl⊩⋆ = reflect⋆ refl⊢⋆

refl⊩⋆′ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ Γ
refl⊩⋆′ = reflect⋆ refl⊢⋆′

mrefl⊩⋆′ : ∀ {Γ Δ} → Γ , Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆′ = reflect⋆ mrefl⊢⋆′

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Π} → Γ , Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ , Δ′ ⊩⋆ Π → Γ , Δ ⊩⋆ Π
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))

refl⊩⋆″ : ∀ {Δ Δ′ Γ Γ′} → (Γ , Δ) Rᶜ (Γ′ , Δ′) → Γ′ , Δ′ ⊩⋆ Δ
refl⊩⋆″ = reflect⋆ ∘ refl⊢⋆″


-- Completeness, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ᴹ⊩ A → Γ ⁏ Δ ⊢ A
quot t = reify (t refl⊩⋆′ refl⊩⋆″)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval
