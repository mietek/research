module BasicIS4.Metatheory.Hilbert-TarskiOvergluedHilbert where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiOvergluedHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ} → Γ ⊢ A → Γ [⊢] A
  [ var i ]   = [var] i
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ box t ]   = [box] [ t ]
  [ cdist ]   = [cdist]
  [ cup ]     = [cup]
  [ cdown ]   = [cdown]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ tt ]      = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = K ([ci] , I)
eval ck        γ = K ([ck] , ⟪K⟫)
eval cs        γ = K ([cs] , ⟪S⟫′)
eval (box t)   γ = K ([ box t ] , eval t ∙)
eval cdist     γ = K ([cdist] , _⟪D⟫′_)
eval cup       γ = K ([cup] , ⟪↑⟫)
eval cdown     γ = K ([cdown] , ⟪↓⟫)
eval cpair     γ = K ([cpair] , _⟪,⟫′_)
eval cfst      γ = K ([cfst] , π₁)
eval csnd      γ = K ([csnd] , π₂)
eval tt        γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_    = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ  = mono⊢
      ; _[⊢]_   = _⊢_
      ; mono[⊢] = mono⊢
      ; [var]    = var
      ; [app]    = app
      ; [ci]     = ci
      ; [ck]     = ck
      ; [cs]     = cs
      ; [box]    = box
      ; [cdist]  = cdist
      ; [cup]    = cup
      ; [cdown]  = cdown
      ; [cpair]  = cpair
      ; [cfst]   = cfst
      ; [csnd]   = csnd
      ; [tt]     = tt
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = t , t
  reflectᶜ {A ▻ B} t = λ η → let t′ = mono⊢ η t
                              in  t′ , λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η → let t′ = mono⊢ η t
                              in  t′ , reflectᶜ (down t′)
  reflectᶜ {A ∧ B} t = reflectᶜ (fst t) , reflectᶜ (snd t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reifyᶜ {α P}   (t , s) = t
  reifyᶜ {A ▻ B} s       = let t , f = s refl⊆ in t
  reifyᶜ {□ A}   s       = let t , a = s refl⊆ in t
  reifyᶜ {A ∧ B} (a , b) = pair (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    ∙       = tt

reifyᶜ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Π , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

reflectᶜ⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Π , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


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
