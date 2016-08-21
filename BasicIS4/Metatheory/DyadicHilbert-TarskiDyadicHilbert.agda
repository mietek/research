module BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicHilbert where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiDyadicHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]   = [var] i
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ mvar i ]  = [mvar] i
  [ box t ]   = [box] [ t ]
  [ cdist ]   = [cdist]
  [ cup ]     = [cup]
  [ cdown ]   = [cdown]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ tt ]      = [tt]


-- Additional useful equipment.

module _ {{_ : Model}} where
  [mmulticut] : ∀ {Π A Γ Δ} → Γ ⁏ Δ [⊢]⋆ □⋆ Π → Γ ⁏ Π [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut] {⌀}     ∙        u = mmono[⊢] bot⊆ u
  [mmulticut] {Π , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci        γ δ = const₂ ([ci] , id)
eval ck        γ δ = const₂ ([ck] , ⟪const⟫)
eval cs        γ δ = const₂ ([cs] , ⟪ap⟫′)
eval (mvar i)  γ δ = mlookup i δ
eval (box t)   γ δ = λ η θ → let δ′ = mono²⊩⋆ (η , θ) δ
                              in  [mmulticut] (reifyʳ⋆ δ′) [ box t ] ,
                                    eval t ∙ δ′
eval cdist     γ δ = const₂ ([cdist] , _⟪◎⟫′_)
eval cup       γ δ = const₂ ([cup] , ⟪⇑⟫)
eval cdown     γ δ = const₂ ([cdown] , ⟪⇓⟫)
eval cpair     γ δ = const₂ ([cpair] , _⟪,⟫′_)
eval cfst      γ δ = const₂ ([cfst] , π₁)
eval csnd      γ δ = const₂ ([csnd] , π₂)
eval tt        γ δ = ∙


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
      ; [app]     = app
      ; [ci]      = ci
      ; [ck]      = ck
      ; [cs]      = cs
      ; [mvar]    = mvar
      ; [box]     = box
      ; [cdist]   = cdist
      ; [cup]     = cup
      ; [cdown]   = cdown
      ; [cpair]   = cpair
      ; [cfst]    = cfst
      ; [csnd]    = csnd
      ; [tt]      = tt
      ; [mlam]    = mlam
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
