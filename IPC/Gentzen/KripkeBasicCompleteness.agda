module IPC.Gentzen.KripkeBasicCompleteness where

open import IPC.Gentzen.KripkeSoundness public


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊪ᵅ_   = λ Γ P → Γ ⊢ α P
    ; mono⊪ᵅ = mono⊢
    ; _‼_     = λ Γ A → Γ ⊢ A
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = return {α P} t
  reflect {A ▷ B} t = return {A ▷ B} (λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a)))
  reflect {A ∧ B} t = return {A ∧ B} (reflect {A} (fst t) , reflect {B} (snd t))
  reflect {⊤}    t = return {⊤} ∙
  reflect {⊥}    t = λ ξ k → boom (mono⊢ ξ t)
  reflect {A ∨ B} t = λ ξ k → case (mono⊢ ξ t)
                                 (k weak⊆ (ι₁ (reflect {A} v₀)))
                                 (k weak⊆ (ι₂ (reflect {B} (v₀))))

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   k = k refl≤ (λ ξ s → s)
  reify {A ▷ B} k = k refl≤ (λ ξ s → lam (reify {B} (s weak⊆ (reflect {A} (v₀)))))
  reify {A ∧ B} k = k refl≤ (λ ξ s → pair (reify {A} (π₁ s)) (reify {B} (π₂ s)))
  reify {⊤}    k = k refl≤ (λ ξ s → tt)
  reify {⊥}    k = k refl≤ (λ ξ ())
  reify {A ∨ B} k = k refl≤ (λ ξ s → κ s
                                        (λ a → inl (reify {A} (λ ξ′ k → a ξ′ k)))
                                        (λ b → inr (reify {B} (λ ξ′ k → b ξ′ k))))

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
