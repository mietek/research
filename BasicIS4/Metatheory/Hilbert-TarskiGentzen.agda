module BasicIS4.Metatheory.Hilbert-TarskiGentzen where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiGentzen public

import BasicIS4.Metatheory.Gentzen-TarskiGentzen as G

open import BasicIS4.Syntax.Translation using (h→g)


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ} → Γ ⊢ A → Γ [⊢] A
  [ t ] = G.[ h→g t ]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = const ([ ci ] , id)
eval ck        γ = const ([ ck ] , ⟪const⟫)
eval cs        γ = const ([ cs ] , ⟪ap⟫′)
eval (box t)   γ = const ([ box t ] , eval t ∙)
eval cdist     γ = const ([ cdist ] , _⟪◎⟫′_)
eval cup       γ = const ([ cup ] , ⟪⇑⟫)
eval cdown     γ = const ([ cdown ] , ⟪⇓⟫)
eval cpair     γ = const ([ cpair ] , _⟪,⟫′_)
eval cfst      γ = const ([ cfst ] , π₁)
eval csnd      γ = const ([ csnd ] , π₂)
eval tt        γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_      = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ    = mono⊢
      ; _[⊢]_     = _⊢_
      ; _[⊢⋆]_    = _⊢⋆_
      ; mono[⊢]   = mono⊢
      ; [var]      = var
      ; [lam]      = lam
      ; [app]      = app
      ; [multibox] = multibox
      ; [down]     = down
      ; [pair]     = pair
      ; [fst]      = fst
      ; [snd]      = snd
      ; [tt]       = tt
      ; top[⊢⋆]   = refl
      ; pop[⊢⋆]   = refl
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflectᶜ {α P}   t = t , t
  reflectᶜ {A ▻ B} t = λ η →
                        let t′ = mono⊢ η t
                        in  t′ , λ a → reflectᶜ (app t′ (reifyᶜ a))
  reflectᶜ {□ A}   t = λ η →
                        let t′ = mono⊢ η t
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
