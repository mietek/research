module New.BasicIPC.Metatheory.Open.HilbertTree.Kripke.Godel where

open import New.BasicIPC.Syntax.Open.HilbertTree public
open import New.BasicIPC.Semantics.Kripke.Godel public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)          γ = lookup i γ
eval (app t u)        γ = (eval t γ refl≤) (eval u γ)
eval ci               γ = λ _ → id
eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                          let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                              g′ = mono⊩ {A ▻ B} ξ′ g
                          in  (f′ refl≤ a refl≤) (g′ refl≤ a)
eval (cpair {A} {B})  γ = λ _ a ξ b ξ′ → mono⊩ {A} (trans≤ ξ ξ′) a , mono⊩ {B} ξ′ b
eval cfst             γ = λ _ s → π₁ (s refl≤)
eval csnd             γ = λ _ s → π₂ (s refl≤)
eval tt               γ = λ _ → ∙


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
  reflect {A ▻ B} t = λ η a → reflect {B} (app (mono⊢ η t) (reify {A} a))
  reflect {A ∧ B} t = λ η → reflect {A} (fst (mono⊢ η t)) , reflect {B} (snd (mono⊢ η t))
  reflect {⊤}    t = λ η → ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s refl⊆
  reify {A ▻ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {A ∧ B} s = pair (reify {A} (π₁ (s refl⊆))) (reify {B} (π₂ (s refl⊆)))
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

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
