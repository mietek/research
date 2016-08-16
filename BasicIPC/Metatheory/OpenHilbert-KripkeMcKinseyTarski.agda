module BasicIPC.Metatheory.OpenHilbert-KripkeMcKinseyTarski where

open import BasicIPC.Syntax.OpenHilbert public
open import BasicIPC.Semantics.KripkeMcKinseyTarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval (var i)          γ = lookup i γ
eval (app t u)        γ = (eval t γ refl≤) (eval u γ)
eval ci               γ = λ _ → id
eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                          let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                              g′ = mono⊩ {A ▻ B} ξ′ g
                          in  (f′ refl≤ a refl≤) (g′ refl≤ a)
eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
eval cfst             γ = λ _ → π₁
eval csnd             γ = λ _ → π₂
eval tt               γ = ∙

-- Alternative version.
eval′ : ∀ {A Γ} → Γ ⊢ A → ∀ᴹʷ⊩ Γ ⇒ A
eval′ (var i)           γ = lookup i γ
eval′ (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval′ t γ) (eval′ u γ)
eval′ ci                γ = const id
eval′ (ck {A} {B})      γ = const (⟪const⟫ {A} {B})
eval′ (cs {A} {B} {C})  γ = const (⟪ap⟫ {A} {B} {C})
eval′ (cpair {A} {B})   γ = const (_⟪,⟫_ {A} {B})
eval′ cfst              γ = const π₁
eval′ csnd              γ = const π₂
eval′ tt                γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᵅ_   = λ Γ P → Γ ⊢ α P
    ; mono⊩ᵅ = mono⊢
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = t
  reflect {A ▻ B} t = λ η a → reflect {B} (app (mono⊢ η t) (reify {A} a))
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▻ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {A ∧ B} s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
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

quot : ∀ {A Γ} → ∀ᴹʷ⊩ Γ ⇒ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
