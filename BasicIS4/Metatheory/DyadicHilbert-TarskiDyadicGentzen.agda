module BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicGentzen where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiDyadicGentzen public

import BasicIS4.Metatheory.DyadicGentzen-TarskiDyadicGentzen as DG

open import BasicIS4.Syntax.Translation using (dh→dg)


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ t ] = DG.[ dh→dg t ]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci        γ δ = K² ([ ci ] , I)
eval ck        γ δ = K² ([ ck ] , ⟪K⟫)
eval cs        γ δ = K² ([ cs ] , ⟪S⟫′)
eval (mvar i)  γ δ = mlookup i δ
eval (box t)   γ δ = λ η θ → let δ′ = mono²⊩⋆ (η , θ) δ
                              in [mmulticut] (reifyʳ⋆ δ′) [ box t ] ,
                                   eval t ∙ δ′
eval cdist     γ δ = K² ([ cdist ] , _⟪D⟫′_)
eval cup       γ δ = K² ([ cup ] , ⟪↑⟫)
eval cdown     γ δ = K² ([ cdown ] , ⟪↓⟫)
eval cpair     γ δ = K² ([ cpair ] , _⟪,⟫′_)
eval cfst      γ δ = K² ([ cfst ] , π₁)
eval csnd      γ δ = K² ([ csnd ] , π₂)
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
