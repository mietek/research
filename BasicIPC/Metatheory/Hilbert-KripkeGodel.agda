module BasicIPC.Metatheory.Hilbert-KripkeGodel where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.KripkeGodel public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval ci                γ = const id
eval (ck {A} {B})      γ = const (⟪const⟫ {A} {B})
eval (cs {A} {B} {C})  γ = const (⟪ap⟫′ {A} {B} {C})
eval (cpair {A} {B})   γ = const (_⟪,⟫′_ {A} {B})
eval (cfst {A} {B})    γ = const (⟪π₁⟫ {A} {B})
eval (csnd {A} {B})    γ = const (⟪π₂⟫ {A} {B})
eval tt                γ = const ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { World  = Cx Ty
    ; _≤_    = _⊆_
    ; refl≤  = refl⊆
    ; trans≤ = trans⊆
    ; _⊩ᵅ_  = λ Γ P → Γ ⊢ α P
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = λ η → mono⊢ η t
  reflect {A ▻ B} t = λ η a → reflect (app (mono⊢ η t) (reify a))
  reflect {A ∧ B} t = λ η →
                        let t′ = mono⊢ η t
                        in  reflect (fst t′) , reflect (snd t′)
  reflect {⊤}    t = λ η → ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s refl⊆
  reify {A ▻ B} s = lam (reify (s weak⊆ (reflect {A} v₀)))
  reify {A ∧ B} s = pair (reify (π₁ (s refl⊆))) (reify (π₂ (s refl⊆)))
  reify {⊤}    s = tt

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


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
