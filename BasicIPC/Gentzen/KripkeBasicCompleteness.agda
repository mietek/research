module BasicIPC.Gentzen.KripkeBasicCompleteness where

open import BasicIPC.Gentzen.KripkeSoundness public




-- Using forcing based on the Gödel translation of IPC to S4.

module GodelBasicCompleteness where
  open GodelSoundness public


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




-- Using satisfaction based on the McKinsey-Tarski translation of IPC to S4.

module McKinseyTarskiBasicCompleteness where
  open McKinseyTarskiSoundness public


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

  quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
  quot t = reify (t refl⊩⋆)


  -- Normalisation by evaluation.

  norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
  norm = quot ∘ eval
