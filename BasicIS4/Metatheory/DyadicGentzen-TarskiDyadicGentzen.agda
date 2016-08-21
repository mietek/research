module BasicIS4.Metatheory.DyadicGentzen-TarskiDyadicGentzen where

open import BasicIS4.Syntax.DyadicGentzen public
open import BasicIS4.Semantics.TarskiDyadicGentzen public



-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]     = [var] i
  [ lam t ]     = [lam] [ t ]
  [ app t u ]   = [app] [ t ] [ u ]
  [ mvar i ]    = [mvar] i
  [ box t ]     = [box] [ t ]
  [ unbox t u ] = [unbox] [ t ] [ u ]
  [ pair t u ]  = [pair] [ t ] [ u ]
  [ fst t ]     = [fst] [ t ]
  [ snd t ]     = [snd] [ t ]
  [ tt ]        = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ η θ → let γ′ = mono²⊩⋆ (η , θ) γ in
                                let δ′ = mono²⊩⋆ (η , θ) δ
                                in  [multicut²] (reifyʳ⋆ γ′) (reifyʳ⋆ δ′) [ lam t ] , λ a →
                                      eval t (γ′ , a) δ′
eval (app t u)   γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval (mvar i)    γ δ = mlookup i δ
eval (box t)     γ δ = λ η θ → let γ′ = mono²⊩⋆ (η , θ) γ in
                                let δ′ = mono²⊩⋆ (η , θ) δ
                                in  [multicut²] (reifyʳ⋆ γ′) (reifyʳ⋆ δ′) [ box t ] ,
                                      eval t ∙ δ′
eval (unbox t u) γ δ = eval u γ (δ , eval t γ δ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⁏_⊩ᵅ_   = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
      ; mono⊩ᵅ   = mono⊢
      ; mmono⊩ᵅ  = mmono⊢
      ; _⁏_[⊢]_  = _⁏_⊢_
      ; mono[⊢]  = mono⊢
      ; mmono[⊢] = mmono⊢
      ; [var]     = var
      ; [lam]     = lam
      ; [app]     = app
      ; [mvar]    = mvar
      ; [box]     = box
      ; [unbox]   = unbox
      ; [pair]    = pair
      ; [fst]     = fst
      ; [snd]     = snd
      ; [tt]      = tt
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = t , t
  reflectᶜ {A ▻ B} t = λ η θ → let t′ = mono²⊢ (η , θ) t
                                in  t′ , λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η θ → let t′ = mono²⊢ (η , θ) t
                                in  t′ , reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reifyᶜ {α P}   (t , s) = t
  reifyᶜ {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reifyᶜ {□ A}   s       = let t , a = s refl⊆ refl⊆ in t
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reflectᶜ⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflectᶜ⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Π} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Π → Γ ⁏ Δ ⊩⋆ Π
trans⊩⋆ ts us = reflectᶜ⋆ (trans⊢⋆ (reifyᶜ⋆ ts) (reifyᶜ⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reifyᶜ (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
