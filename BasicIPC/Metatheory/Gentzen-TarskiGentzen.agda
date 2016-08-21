module BasicIPC.Metatheory.Gentzen-TarskiGentzen where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiGentzen public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflectʳ : ∀ {A Γ} → Γ ⊢ A → [ Γ ⊢ A ]
  reflectʳ (var i)    = [var] i
  reflectʳ (lam t)    = [lam] (reflectʳ t)
  reflectʳ (app t u)  = [app] (reflectʳ t) (reflectʳ u)
  reflectʳ (pair t u) = [pair] (reflectʳ t) (reflectʳ u)
  reflectʳ (fst t)    = [fst] (reflectʳ t)
  reflectʳ (snd t)    = [snd] (reflectʳ t)
  reflectʳ tt         = [tt]


-- Additional useful equipment.

module _ {{_ : Model}} where
  [multicut] : ∀ {Π A Γ} → [ Γ ⊢ Π ]⋆ → [ Π ⊢ A ] → [ Γ ⊢ A ]
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ η → let γ′ = mono⊩⋆ η γ
                           in  [multicut] (reifyʳ⋆ γ′) (reflectʳ (lam t)) , λ a →
                                 eval t (γ′ , a)
eval (app t u)  γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊩ᵅ_    = λ Γ P → Γ ⊢ α P
    ; mono⊩ᵅ  = mono⊢
    ; [_⊢_]   = _⊢_
    ; mono[⊢] = mono⊢
    ; [var]    = var
    ; [lam]    = lam
    ; [app]    = app
    ; [pair]   = pair
    ; [fst]    = fst
    ; [snd]    = snd
    ; [tt]     = tt
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = t , t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  t′ , λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   (t , s) = t
  reifyᶜ {A ▻ B} s       = let t , f = s refl⊆ in t
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reifyᶜ (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
